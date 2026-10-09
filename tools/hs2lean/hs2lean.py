"""hs2lean: translate l4v's Haskell kernel model into Lean 4 (C3, crawl).

    hs2lean.py types  STRUCTURES.lhs TYPE [TYPE ...]        > Structures.lean
    hs2lean.py module MODULE.lhs --types STRUCTURES.lhs ... > Module.lean

Parsing uses tree-sitter-haskell. Anything the translator does not handle raises `Unsupported` with the
node type and source line; it never guesses. Operator chains are re-associated with Haskell fixities,
because tree-sitter does not resolve them.

Output targets `Sel4Lean.Exec` (Prelude.lean, Stubs.lean): the Haskell `Kernel` monad becomes l4v's
nondeterministic `Kernel := NondetM KernelState`, so Lean `do` keeps the Haskell structure.
"""
import sys
from tree_sitter import Language, Parser
import tree_sitter_haskell

PARSER = Parser(Language(tree_sitter_haskell.language()))


class Unsupported(Exception):
    pass


# ---------------------------------------------------------------- parsing

def unlit(text: str) -> str:
    """Literate Haskell (bird tracks) -> plain Haskell, keeping line numbers."""
    out = []
    for line in text.splitlines():
        out.append(line[2:] if line.startswith("> ") else "")
    return "\n".join(out) + "\n"


def parse_file(path: str):
    text = open(path).read()
    if path.endswith(".lhs"):
        text = unlit(text)
    src = text.encode()
    return src, PARSER.parse(src).root_node


def kids(node):
    """Named children, minus comments (they carry no meaning for the translation)."""
    return [c for c in node.named_children if c.type != "comment"]


def node_name(node, src):
    n = node.child_by_field_name("name")
    return src[n.start_byte:n.end_byte].decode() if n else None


def top_decls(src, root):
    """Yield (name, [nodes]) for top-level declarations, grouping a signature with its equations."""
    decls = next((c for c in root.children if c.type == "declarations"), None)
    if decls is None:
        return
    groups, order = {}, []
    for d in kids(decls):
        name = node_name(d, src)
        if name is None:
            continue
        if name not in groups:
            groups[name] = []
            order.append(name)
        groups[name].append(d)
    for name in order:
        yield name, groups[name]


# ---------------------------------------------------------------- tables

# Haskell fixities (Prelude, Data.Bits, Data.List). Unknown operators are refused.
FIXITY = {
    "$": ("r", 0), ">>=": ("l", 1), ">>": ("l", 1), "||": ("r", 2), "&&": ("r", 3),
    "==": ("n", 4), "/=": ("n", 4), "<": ("n", 4), "<=": ("n", 4), ">": ("n", 4), ">=": ("n", 4),
    "<$>": ("l", 4), ":": ("r", 5), "++": ("r", 5), ".|.": ("l", 5), "xor": ("l", 6),
    "+": ("l", 6), "-": ("l", 6), ".&.": ("l", 7), "*": ("l", 7), ".": ("r", 9),
    "shiftL": ("l", 8), "shiftR": ("l", 8), "!": ("l", 9), "!!": ("l", 9), "//": ("l", 9),
    "=<<": ("r", 1), "<*>": ("l", 4), "$!": ("r", 0), "^": ("r", 8),
}
DEFAULT_FIXITY = ("l", 9)   # Haskell's default for backtick functions without a fixity declaration
# Haskell operator -> Lean operator (None: function application, handled specially)
OPERATOR = {
    "$": None, "||": "||", "&&": "&&", "==": "==", "/=": "!=", "<": "<", "<=": "≤", ">": ">", ">=": "≥",
    ":": "::", "++": "++", ".|.": "|||", ".&.": "&&&", "+": "+", "-": "-", "*": "*",
    ".": "∘", ">>=": ">>=", ">>": ">>=", "^": "^",
}
# operators rendered as function application: Haskell op -> Lean function (None: plain application)
OPERATOR_APP = {"!": None, "$!": None, "!!": "listIndexH", "//": "arrayUpdH", "=<<": "flip bind", "<*>": "seqH",
                # shifts as functions, so the expected result type reaches the shifted operand
                "shiftL": "shiftLH", "shiftR": "shiftRH"}
# Haskell names -> Lean names (Prelude.lean)
NAME = {
    "return": "pure", "fail": "failH", "assert": "assertH", "stateAssert": "stateAssertH",
    "forM_": "forM_H", "delete": "deleteH", "when": "whenH", "unless": "unlessH", "break": "breakH",
    "fromPPtr": "PPtr.ptr", "PPtr": "PPtr.mk",
    # mtl classes -> Lean's monad classes
    "throwError": "MonadExcept.throw", "catchError": "MonadExcept.tryCatch", "runExceptT": "ExceptT.run",
    "ask": "read",
    "Left": "Except.error", "Right": "Except.ok",
    "Just": "some", "Nothing": "none", "True": "true", "False": "false",
}
TYPE = {"Maybe": "Option", "Bool": "Bool", "Word": "Word", "Int": "Int", "Integer": "Int"}
LEAN_KEYWORDS = {"at", "by", "do", "else", "end", "for", "from", "fun", "have", "if", "in", "let",
                 "match", "open", "then", "with", "where", "show", "from", "λ", "Type", "Prop",
                 "break", "continue", "return", "mut", "unless", "try", "catch", "finally", "instance",
                 "structure", "class", "inductive", "theorem", "def", "namespace", "section", "variable",
                 "universe", "deriving", "calc", "suffices", "obtain", "termination_by", "decreasing_by"}


class DataInfo:
    """Constructors and fields of the translated data types, used to resolve names."""

    def __init__(self):
        self.types = {}      # type -> {"ctors": [(ctor, [(field, type_node)] or None, [arg type nodes])], "single": bool}
        self.ctor_type = {}  # ctor -> type
        self.arch_ctor_type = {}  # ctor -> RISCV64.T, for constructors of arch types (shadowing generic ones)
        self.integral = set()     # types with an IntegralH instance (newtypes over words, enums)
        self.deferred = []        # instance lines to emit after everything else (full.py)
        self.field_type = {} # field -> type


# ---------------------------------------------------------------- translator

class Translator:
    def __init__(self, src, data: DataInfo):
        self.src = src
        self.data = data

    def text(self, n):
        return self.src[n.start_byte:n.end_byte].decode()

    def fail(self, n, what="unsupported"):
        line = n.start_point[0] + 1
        raise Unsupported(f"{what}: {n.type} at line {line}: {self.text(n)[:80]!r}")

    @staticmethod
    def ident(name):
        return f"«{name}»" if name in LEAN_KEYWORDS else name

    # ---------------- types

    def ty(self, n):
        t = n.type
        if t == "name":
            name = self.text(n)
            return TYPE.get(name, name)
        if t == "unit":
            return "Unit"
        if t == "list":
            return f"List {self.ty_atom(n.child_by_field_name('element'))}"
        if t == "apply":
            f = n.child_by_field_name("constructor")
            a = n.child_by_field_name("argument")
            return f"{self.ty(f)} {self.ty_atom(a)}"
        if t == "function":
            p = n.child_by_field_name("parameter")
            r = n.child_by_field_name("result")
            return f"{self.ty_atom(p)} → {self.ty(r)}"
        if t == "parens":
            return self.ty(kids(n)[0])
        if t == "tuple":
            return " × ".join(self.ty_atom(c) for c in kids(n))
        self.fail(n, "type")

    def ty_atom(self, n):
        s = self.ty(n)
        return f"({s})" if " " in s else s

    # ---------------- data declarations

    def collect_data(self, name, node):
        ctors = []
        cs = node.child_by_field_name("constructors")
        if cs is None:
            self.fail(node, "data type without constructors")
        for dc in kids(cs):
            if dc.type != "data_constructor":
                self.fail(dc)
            c = dc.child_by_field_name("constructor")
            cname = node_name(c, self.src)
            if c.type == "prefix":
                args = [x for x in kids(c) if x.type != "constructor"]
                ctors.append((cname, None, args))
            elif c.type == "record":
                fields = []
                for f in kids(c.child_by_field_name("fields")):
                    ftype = f.child_by_field_name("type")
                    # `a, b :: T` declares several fields of one type
                    names = [x for x in kids(f) if x.type == "field_name"] or [f.child_by_field_name("name")]
                    for nm in names:
                        fields.append((self.text(nm), ftype))
                ctors.append((cname, fields, [t for _, t in fields]))
            else:
                self.fail(c)
        info = {"ctors": ctors, "single": len(ctors) == 1 and ctors[0][1] is not None}
        self.data.types[name] = info
        for cname, fields, _ in ctors:
            if name.startswith("RISCV64."):
                self.data.arch_ctor_type[cname] = name
                self.data.ctor_type.setdefault(cname, name)
            else:
                self.data.ctor_type[cname] = name
            for fname, _ in fields or []:
                self.data.field_type[fname] = name

    def emit_data(self, name, node):
        info = self.data.types[name]
        # DecidableEq whenever derivable (Haskell sometimes hand-writes `instance Eq`); full.py drops it
        # again for types that contain functions
        derives = "deriving Inhabited, DecidableEq"
        out = []
        if info["single"]:
            cname, fields, _ = info["ctors"][0]
            out.append(f"/-- Haskell `data {name} = {cname} {{ … }}` -/")
            out.append(f"structure {name} where")
            out.append(f"  {cname} ::")   # keep the Haskell constructor name
            for fname, ft in fields:
                out.append(f"  {fname} : {self.ty(ft)}")
            out.append(f"  {derives}")
            return "\n".join(out)
        out.append(f"/-- Haskell `data {name}` -/")
        out.append(f"inductive {name} where")
        for cname, fields, args in info["ctors"]:
            if fields:
                out.append(f"  | {cname} " + " ".join(f"({f} : {self.ty(t)})" for f, t in fields))
            else:
                out.append(f"  | {cname}" + "".join(f" (a{i} : {self.ty(t)})" for i, t in enumerate(args)))
        out.append(f"  {derives}")
        if all(not args and not fields for _, fields, args in info["ctors"]):
            # enumeration: Haskell `Enum`/`fromIntegral` via the constructor index Lean generates
            out.append("")
            cs = [c for c, _, _ in info["ctors"]]
            to = " ".join(f"| .{c} => {i}" for i, c in enumerate(cs))
            of = " ".join(f"| {i} => .{c}" for i, c in enumerate(cs))
            q = f"_root_.Sel4Lean.Spec.{name}"   # a constructor may share the type's name (data UserData = UserData)
            out.append(f"def {name}.toIdx : {q} → Int {to}")
            out.append(f"def {name}.ofIdx : Nat → {q} {of} | _ => default")
            out.append(f"instance : IntegralH {q} := ⟨{name}.toIdx, fun i => {name}.ofIdx i.toNat⟩")
            out.append(f"instance : BoundedH {q} := ⟨.{cs[0]}, .{cs[-1]}⟩")
        # Haskell field selectors and record update, per field (fields may be shared by constructors)
        fields_all = {}
        for cname, fields, args in info["ctors"]:
            for i, (fname, ft) in enumerate(fields or []):
                fields_all.setdefault(fname, (ft, []))[1].append((cname, i, len(fields)))
        for fname, (ft, owners) in fields_all.items():
            total = len(owners) == len(info["ctors"])
            fty = self.ty(ft)
            out.append("")
            out.append(f"/-- Haskell selector `{fname}`; on other constructors unspecified (`undefinedH`), as l4v's "
                       f"primrec selectors are in Isabelle. -/")
            out.append(f"def {name}.{fname} : {name} → {fty}")
            for cname, i, n in owners:
                pats = " ".join("v" if j == i else "_" for j in range(n))
                out.append(f"  | .{cname} {pats} => v")
            if not total:
                out.append("  | _ => undefinedH" if getattr(self, "l4v_style", False) else "  | _ => default")
            out.append(f"/-- Haskell record update `x {{ {fname} = v }}` (no-op on other constructors). -/")
            out.append(f"def {name}.set_{fname} (x : {name}) (v : {fty}) : {name} :=")
            out.append("  match x with")
            for cname, i, n in owners:
                pats = " ".join("_" if j == i else f"a{j}" for j in range(n))
                args = " ".join("v" if j == i else f"a{j}" for j in range(n))
                out.append(f"  | .{cname} {pats} => .{cname} {args}")
            if not total:
                out.append("  | x => x")
        # l4v's translator (lhs_pars.py named_constructor_check) gives every constructor of a record-syntax
        # data type with several constructors a discriminator `isC v ≡ case v of C … ⇒ True | _ ⇒ False`
        if getattr(self, "l4v_style", False) and len(info["ctors"]) > 1 and any(f for _, f, _ in info["ctors"]):
            ns = name.rsplit(".", 1)[0] + "." if "." in name else ""
            ps = self.params(node) if hasattr(self, "params") else []
            binders = "".join(f" {{{p} : Type}}" for p in ps)
            applied = f"(_root_.Sel4Lean.Spec.{name} {' '.join(ps)})" if ps else f"_root_.Sel4Lean.Spec.{name}"
            for cname, fields, args in info["ctors"]:
                out.append("")
                out.append(f"/-- l4v-generated discriminator `is{cname}` -/")
                out.append(f"def {ns}is{cname}{binders} : {applied} → Bool")
                out.append(f"  | .{cname} .. => true")
                out.append("  | _ => false")
        return "\n".join(out)

    # ---------------- names

    def var(self, name):
        if name in getattr(self, "bound", ()):
            return self.ident(name)   # a local variable, even if a selector or library name is spelled the same
        if name in NAME and name not in getattr(self, "local_names", ()):
            return NAME[name]
        if name in self.data.field_type:
            return f"{self.data.field_type[name]}.{name}"
        return self.ident(name)

    def ctor(self, name):
        if name == "Word":
            return "id"   # the spec's `newtype Word = Word Arch.Word` is BitVec 64 itself here
        if name in NAME:
            return NAME[name]
        if name in self.data.ctor_type:
            return f"{self.data.ctor_type[name]}.{name}"
        return name

    # ---------------- patterns

    def pat(self, n):
        t = n.type
        if t == "variable":
            return self.ident(self.text(n))
        if t == "wildcard":
            return "_"
        if t == "constructor":
            return self.ctor(self.text(n))
        if t == "list":
            if n.named_child_count:
                return "[" + ", ".join(self.pat(c) for c in kids(n)) + "]"
            return "[]"
        if t == "tuple":
            return "(" + ", ".join(self.pat(c) for c in kids(n)) + ")"
        if t == "parens":
            return self.pat_atom(kids(n)[0])
        if t == "apply":
            parts = []
            m = n
            while m.type == "apply":
                parts.append(m.child_by_field_name("argument"))
                m = m.child_by_field_name("function")
            if m.type != "constructor":
                self.fail(n, "pattern")
            if self.text(m) == "Word" and len(parts) == 1:
                return self.pat(parts[0])   # the spec's `newtype Word` is BitVec 64 itself here
            return " ".join([self.ctor(self.text(m))] + [self.pat_atom(p) for p in reversed(parts)])
        if t == "as":
            v = n.child_by_field_name("bind") or kids(n)[0]
            p = n.child_by_field_name("pattern") or kids(n)[-1]
            return f"{self.ident(self.text(v))}@{self.pat_atom(p)}"
        if t == "infix":
            op = self.text(n.child_by_field_name("operator"))
            if op != ":":
                self.fail(n, "pattern operator")
            return f"{self.pat_atom(n.child_by_field_name('left_operand'))} :: {self.pat(n.child_by_field_name('right_operand'))}"
        if t == "record":
            c = n.child_by_field_name("constructor")
            fps = [x for x in kids(n) if x.type == "field_pattern"]
            if c is None:
                self.fail(n, "record pattern without constructor")
            if not fps:
                cname = self.text(c).split(".")[-1]
                tname = self.data.ctor_type.get(cname)
                if ".." in self.text(n) and tname is not None:
                    # `C {..}` (RecordWildCards) binds every field under its own name
                    cfields = next(fs for cn, fs, _ in self.data.types[tname]["ctors"] if cn == cname)
                    if self.data.types[tname]["single"]:
                        return "{ " + ", ".join(f"{f} := {self.ident(f)}" for f, _ in cfields) + " }"
                    return " ".join([self.ctor(cname)] + [self.ident(f) for f, _ in cfields])
                return f"{self.ctor(self.text(c))} .."   # `C {}` matches any C
            cname = self.text(c).split(".")[-1]
            tname = self.data.ctor_type.get(cname)
            if tname is None:
                self.fail(n, "record pattern of unknown constructor")
            cfields = next(fs for cn, fs, _ in self.data.types[tname]["ctors"] if cn == cname)
            given = {}
            for fp in fps:
                parts = kids(fp)
                fname = self.text(fp.child_by_field_name("field") or parts[0]).split(".")[-1]
                sub = fp.child_by_field_name("pattern") or (parts[-1] if len(parts) > 1 else None)
                given[fname] = self.pat_atom(sub) if sub is not None else self.ident(fname)  # punning
            if self.data.types[tname]["single"]:
                return "{ " + ", ".join(f"{f} := {v}" for f, v in given.items()) + ", .. }"
            return " ".join([self.ctor(cname)] + [given.get(f, "_") for f, _ in cfields])
        if t == "literal":
            return self.text(n)
        self.fail(n, "pattern")

    def pat_atom(self, n):
        p = self.pat(n)
        return f"({p})" if " " in p and not p.startswith(("(", "[")) else p

    # ---------------- expressions
    # e(n, ind) returns Lean text whose first line is unindented and later lines are indented by `ind`.

    def e(self, n, ind):
        t = n.type
        if t == "variable":
            return self.var(self.text(n))
        if t == "constructor":
            return self.ctor(self.text(n))
        if t == "literal":
            return self.text(n)
        if t == "unit":
            return "()"
        if t == "qualified":
            base = self.text(n).split(".")[-1]
            return self.var(base) if base[:1].islower() else self.ctor(base)
        if t == "parens":
            return self.e(kids(n)[0], ind)
        if t == "list":
            return "[" + ", ".join(self.e(c, ind) for c in kids(n)) + "]"
        if t == "tuple":
            return "(" + ", ".join(self.e(c, ind) for c in kids(n)) + ")"
        if t == "apply":
            parts = []
            m = n
            while m.type == "apply":
                parts.append(m.child_by_field_name("argument"))
                m = m.child_by_field_name("function")
            return " ".join([self.atom(m, ind)] + [self.atom(a, ind) for a in reversed(parts)])
        if t == "infix":
            return self.infix(n, ind)
        if t == "do":
            return self.do(n, ind)
        if t == "case":
            return self.case(n, ind)
        if t == "conditional":
            c, a, b = (n.child_by_field_name(k) for k in ("if", "then", "else"))
            return (f"if {self.e(c, ind)} then\n{' ' * (ind + 2)}{self.e(a, ind + 2)}\n"
                    f"{' ' * ind}else\n{' ' * (ind + 2)}{self.e(b, ind + 2)}")
        if t == "lambda":
            ps = n.child_by_field_name("patterns")
            body = n.child_by_field_name("expression")
            return f"fun {' '.join(self.pat_atom(p) for p in kids(ps))} => {self.e(body, ind + 2)}"
        if t == "record":
            return self.record(n, ind)
        if t == "signature":   # (e :: T)
            ex = n.child_by_field_name("expression") or kids(n)[0]
            return f"({self.e(ex, ind)} : {self.ty(n.child_by_field_name('type'))})"
        if t == "negation":
            return f"-{self.atom(kids(n)[0], ind)}"
        if t in ("right_section", "left_section"):
            op = next(c for c in n.children if c.type in ("operator", "infix_id", "constructor_operator"))
            name = self.text(op).strip("`")
            arg = next(c for c in kids(n) if c is not op)
            if name in OPERATOR_APP:   # sections of application-like operators: (! r), (// upds)
                f = OPERATOR_APP[name]
                pre = f"{f} " if f else ""
                a = self.atom(arg, ind)
                return (f"(fun x => {pre}x {a})" if t == "right_section" else f"(fun x => {pre}{a} x)")
            lean = OPERATOR.get(name)
            if lean is None:
                fn = self.var(name)
                return (f"(fun x => {fn} x {self.atom(arg, ind)})" if t == "right_section"
                        else f"(fun x => {fn} {self.atom(arg, ind)} x)")
            return (f"(· {lean} {self.atom(arg, ind)})" if t == "right_section"
                    else f"({self.atom(arg, ind)} {lean} ·)")
        if t == "prefix_id":   # (+) used as a function
            name = self.text(n).strip("()` ")
            lean = OPERATOR.get(name)
            if lean is None:
                self.fail(n, f"operator {name!r} as function")
            return f"(· {lean} ·)"
        if t == "let_in":
            binds = n.child_by_field_name("binds")
            body = n.child_by_field_name("expression")
            lines = [lb for lb in (self.local_bind(b, ind) for b in self.ordered_binds(kids(binds))) if lb]
            return ("\n" + " " * ind).join(lines + [self.e(body, ind)])
        if t == "arithmetic_sequence":
            frm = n.child_by_field_name("from")
            to = n.child_by_field_name("to")
            if frm is None or to is None or n.child_by_field_name("step") is not None:
                self.fail(n, "arithmetic sequence form")
            return f"enumFromToH {self.atom(frm, ind)} {self.atom(to, ind)}"
        self.fail(n)

    def atom(self, n, ind):
        s = self.e(n, ind)
        simple = n.type == "literal" or (n.type in ("variable", "constructor", "unit", "list", "tuple") and " " not in s)
        return s if simple else f"({s})"

    def infix(self, n, ind):
        # flatten the chain tree-sitter built, then resolve with Haskell fixities
        operands, ops = [], []

        def walk(m):
            if m.type == "infix":
                walk(m.child_by_field_name("left_operand"))
                ops.append(m.child_by_field_name("operator"))
                walk(m.child_by_field_name("right_operand"))
            else:
                operands.append(m)
        walk(n)
        names = [self.text(o).strip("`") for o in ops]
        self._backtick = {nm for o, nm in zip(ops, names) if o.type == "infix_id"}
        for o, name in zip(ops, names):
            if o.type == "infix_id" and name not in FIXITY:
                FIXITY.setdefault(name, DEFAULT_FIXITY)
            if name not in FIXITY or (name not in OPERATOR and name not in OPERATOR_APP
                                      and o.type != "infix_id"):
                self.fail(o, f"operator {name!r}")

        def build(lo, hi):
            # operands[lo..hi], operators names[lo..hi-1]: split at the loosest-binding operator
            if lo == hi:
                return ("leaf", operands[lo])
            minp = min(FIXITY[names[i]][1] for i in range(lo, hi))
            idxs = [i for i in range(lo, hi) if FIXITY[names[i]][1] == minp]
            assocs = {FIXITY[names[i]][0] for i in idxs}
            if len(assocs) > 1 or (assocs == {"n"} and len(idxs) > 1):
                self.fail(n, "ambiguous operator chain (GHC would reject it too)")
            i = idxs[-1] if assocs == {"l"} else idxs[0]
            return ("op", names[i], build(lo, i), build(i + 1, hi))
        return self.render(build(0, len(operands) - 1), ind)

    def render(self, tree, ind):
        if tree[0] == "leaf":
            return self.e(tree[1], ind)
        _, op, l, r = tree
        if op == ">>":   # a >> b  ==  a >>= fun _ => b
            return f"{self.render_atom(l, ind)} >>= fun _ => {self.render_atom(r, ind)}"
        if op in OPERATOR_APP:
            f = OPERATOR_APP[op]
            parts = [self.render_atom(l, ind), self.render_atom(r, ind)]
            return " ".join(([f] if f else []) + parts)
        if op not in OPERATOR:   # backtick function: a `f` b  ==  f a b
            fn = self.backtick_fn(op)
            return f"{fn} {self.render_atom(l, ind)} {self.render_atom(r, ind)}"
        if op == "$":
            left = self.e(l[1], ind) if l[0] == "leaf" and l[1].type in ("apply", "variable", "constructor") else self.render_atom(l, ind)
            return f"{left} {self.render_atom(r, ind)}"
        return f"{self.render_atom(l, ind)} {OPERATOR[op]} {self.render_atom(r, ind)}"

    def backtick_fn(self, op):
        """Function used in backticks (a `f` b); full.py routes qualified ones (Arch.f)."""
        return self.var(op.split(".")[-1])

    def render_atom(self, tree, ind):
        if tree[0] == "leaf":
            return self.atom(tree[1], ind)
        return f"({self.render(tree, ind)})"

    def record(self, n, ind):
        fields = [c for c in kids(n) if c.type == "field_update"]
        base = n.child_by_field_name("expression")
        ctor = n.child_by_field_name("constructor")
        if base is not None and base.type == "constructor":
            ctor, base = base, None
        upd = []
        for f in fields:
            fname = self.text(f.child_by_field_name("field")).split(".")[-1]
            upd.append((fname, f.child_by_field_name("expression")))
        if ctor is not None and base is None:
            # construction: C { f = v, ... } -> positional
            cname = self.text(ctor)
            tname = self.data.ctor_type.get(cname)
            if tname is None:
                self.fail(n, "record construction of unknown constructor")
            cfields = next(fs for c, fs, _ in self.data.types[tname]["ctors"] if c == cname)
            given = {f.split(".")[-1]: v for f, v in upd}
            if not set(given) <= {f for f, _ in cfields}:
                self.fail(n, "record construction with unknown fields")
            # Haskell allows omitted fields (reading them is bottom); here they are `default`
            if self.data.types[tname]["single"]:
                return "{ " + ", ".join(f"{f} := {self.e(given[f], ind + 2) if f in given else 'default'}"
                                        for f, _ in cfields) + f" : {tname} }}"
            return " ".join([self.ctor(cname)] + [self.atom(given[f], ind) if f in given else "default"
                                                   for f, _ in cfields])
        if base is None:
            self.fail(n, "record expression")
        # update: x { f = v, ... }
        tnames = {self.data.field_type.get(f) for f, _ in upd}
        if len(tnames) != 1 or None in tnames:
            self.fail(n, "record update of unknown field")
        tname = tnames.pop()
        if self.data.types[tname]["single"]:
            inner = ", ".join(f"{f} := {self.e(v, ind + 4)}" for f, v in upd)
            return f"{{ {self.atom(base, ind)} with {inner} }}"
        s = self.atom(base, ind)
        for f, v in upd:
            s = f"{tname}.set_{f} {s if s.startswith('(') or ' ' not in s else '(' + s + ')'} {self.atom(v, ind)}"
            s = f"({s})"
        return s[1:-1]

    def rhs(self, node, ind, last=True):
        """Right-hand side of an equation / binding / alternative: one `match`, or several guarded ones.
        Guards become if-chains; `otherwise`/`True` is the final else. If guards can all fail, the result is
        `default` (Haskell pattern-match failure) for the last equation, and refused otherwise (falling
        through to a later equation has no direct Lean counterpart)."""
        ms = [c for i, c in enumerate(node.children) if node.field_name_for_child(i) == "match"]
        if not ms:
            self.fail(node, "no right-hand side")
        if len(ms) == 1 and ms[0].child_by_field_name("guards") is None:
            return self.e(ms[0].child_by_field_name("expression"), ind)
        branches, final = [], None
        for m in ms:
            gs = m.child_by_field_name("guards")
            body = m.child_by_field_name("expression")
            if gs is None:
                final = body; break
            conds = []
            for g in kids(gs):
                if g.type != "boolean":
                    self.fail(g, "pattern guard")
                c = kids(g)[0]
                if self.text(c) in ("otherwise", "True"):
                    continue
                conds.append(self.atom(c, ind))
            if not conds:
                final = body; break
            branches.append((" && ".join(conds), body))
        if final is None and not last:
            self.fail(node, "guards that fall through to the next equation")
        pad = " " * (ind + 2)
        out = []
        for i, (c, b) in enumerate(branches):
            kw = "if" if i == 0 else "else if"
            out.append(f"{kw} {c} then\n{pad}{self.e(b, ind + 2)}")
        out.append(f"else\n{pad}{self.e(final, ind + 2) if final is not None else 'default'}")
        return ("\n" + " " * ind).join(out)

    def do(self, n, ind):
        stmts = [c for c in kids(n) if c.type in ("bind", "exp", "let")]
        if len(stmts) != len(kids(n)):
            bad = next(c for c in kids(n) if c not in stmts)
            self.fail(bad, "do statement")
        lines = []
        si = ind + 2
        # Haskell `do` scoping is positional: a name bound by statement j is not in scope in statements
        # before j (e.g. `byte <- gets value; …; value <- …` uses the selector `value` first)
        binders_of = getattr(self, "binders_of", None)
        params = getattr(self, "param_names", None)
        outer = getattr(self, "bound", set())
        stmt_binders = []
        if binders_of is not None and params is not None:
            for st in stmts:
                node = st.child_by_field_name("pattern") if st.type == "bind" else (
                    st.child_by_field_name("binds") if st.type == "let" else None)
                stmt_binders.append(binders_of(node) if node is not None else set())
        for i, s in enumerate(stmts):
            if stmt_binders:
                before = set().union(*stmt_binders[:i])
                later = set().union(*stmt_binders[i:]) - before - params
                self.bound = outer - later
            if s.type == "bind":
                pn = s.child_by_field_name("pattern")
                p = self.pat(pn)
                ex = self.e(s.child_by_field_name('expression'), si + 2)
                if pn.type not in ("variable", "tuple", "wildcard", "parens") and getattr(self, "discard_stmts", False):
                    # Haskell MonadFail on a refutable bind; parenthesise so a multi-line `match` does not
                    # swallow the `| failM …` handler as one of its alternatives
                    line = f"let {p} ← ({ex}) | failM \"pattern match failure\""
                else:
                    line = f"let {p} ← {ex}"
                lines.append(line)
            elif s.type == "exp":
                # Haskell drops non-Unit results of non-final statements; Lean needs `let _ ←`. The prefix
                # moves the term 8 columns right, and continuation lines must stay right of the term's start
                discard = getattr(self, "discard_stmts", False) and s is not stmts[-1]
                ex = self.e(kids(s)[0], si + 8 if discard else si)
                lines.append(f"let _ ← {ex}" if discard else ex)
            else:
                for b in self.ordered_binds(kids(s.child_by_field_name("binds"))):
                    lb = self.local_bind(b, si, in_do=True)
                    if lb:
                        lines.append(lb)
        self.bound = outer
        pad = " " * si
        return "do\n" + "\n".join(pad + l for l in lines)

    def ordered_binds(self, binds):
        """Haskell `where`/`let` groups are order-independent; Lean `let`s are sequential: sort by use."""
        binds = [b for b in binds if b.type != "signature"]
        def defined(b):
            n = b.child_by_field_name("name")
            if n is not None:
                return {self.text(n)}
            p = b.child_by_field_name("pattern")
            out, st = set(), [p] if p is not None else []
            while st:
                m = st.pop()
                if m.type == "variable":
                    out.add(self.text(m))
                st.extend(m.named_children)
            return out
        def used(b):
            out, st = set(), [c for i, c in enumerate(b.children) if b.field_name_for_child(i) == "match"]
            while st:
                m = st.pop()
                if m.type == "variable":
                    out.add(self.text(m))
                st.extend(m.named_children)
            return out
        defs = [defined(b) for b in binds]
        owner = {v: i for i, d in enumerate(defs) for v in d}
        deps = [{owner[v] for v in used(b) if v in owner} - {i} for i, b in enumerate(binds)]
        order, state = [], {}
        def visit(i):
            if state.get(i) == 2:
                return
            if state.get(i) == 1:
                self.fail(binds[i], "mutually recursive local bindings")
            state[i] = 1
            for j in sorted(deps[i]):
                visit(j)
            state[i] = 2
            order.append(binds[i])
        for i in range(len(binds)):
            visit(i)
        return order

    def local_bind(self, b, ind, in_do=False):
        if b.type == "signature":
            return None   # local type annotation: Lean infers it
        if b.type == "bind" and b.child_by_field_name("name") is None:
            pat = b.child_by_field_name("pattern")   # destructuring: (l, h) = e
            if pat.type not in ("variable", "tuple", "wildcard") and in_do:
                # Haskell `let Just p = e` is lazy/irrefutable; a failed match is bottom: fail here
                return f"let {self.pat(pat)} := {self.rhs(b, ind + 2)} | failM \"irrefutable pattern\""
            return f"let {self.pat(pat)} := {self.rhs(b, ind + 2)}"
        if b.type == "bind":
            name = self.ident(self.text(b.child_by_field_name("name")))
            return f"let {name} := {self.rhs(b, ind + 2)}"
        if b.type == "function":
            name = self.ident(self.text(b.child_by_field_name("name")))
            ps = kids(b.child_by_field_name("patterns"))
            return f"let {name} := fun {' '.join(self.pat_atom(p) for p in ps)} =>\n{' ' * (ind + 2)}{self.rhs(b, ind + 2)}"
        self.fail(b, "local binding")

    def case(self, n, ind):
        scrut = next(c for c in kids(n) if c.type != "alternatives")
        alts = n.child_by_field_name("alternatives")
        lines = [f"match {self.e(scrut, ind + 2)} with"]
        for a in kids(alts):
            p = self.pat(a.child_by_field_name("pattern"))
            ms = [c for i, c in enumerate(a.children) if a.field_name_for_child(i) == "match"]
            guarded = len(ms) > 1 or ms[0].child_by_field_name("guards") is not None
            if guarded:
                # Haskell falls through to the next alternative when all guards fail; refuse unless
                # this is the last alternative or an `otherwise` closes the chain
                b = "(" + self.rhs(a, ind + 4, last=(a == kids(alts)[-1])) + ")"
            else:
                body = ms[0].child_by_field_name("expression")
                b = self.e(body, ind + 4)
                if body.type in ("case", "do", "conditional", "lambda"):
                    b = f"({b})"
            lines.append(f"{' ' * ind}| {p} => {b}")
        return "\n".join(lines)

    # ---------------- functions

    def emit_function(self, name, nodes, sig_override=None):
        """sig_override = (param type strings, result string): a signature translated elsewhere (an arch function
        borrowing its generic signature, resolved in the arch file's scope)."""
        sig = next((d for d in nodes if d.type == "signature"), None)
        eqs = [d for d in nodes if d.type in ("function", "bind")]
        if not eqs:
            self.fail(nodes[0], "no equations")
        if sig is None and sig_override is not None:
            return self._emit_with(name, eqs, sig_override[0], sig_override[1])
        if sig is None:
            if len(eqs) == 1 and eqs[0].type == "bind":
                # top-level constant without a signature: let Lean infer the type
                return f"/-- Haskell `{name}` -/\ndef {self.ident(name)} :=\n  {self.rhs(eqs[0], 2)}"
            self.fail(nodes[0], "function without a signature")
        params, t = [], sig.child_by_field_name("type")
        if t.type == "context":
            t = t.child_by_field_name("type")
        while t.type == "function":
            params.append(t.child_by_field_name("parameter"))
            t = t.child_by_field_name("result")
        return self._emit_with(name, eqs, [self.ty(p) for p in params], self.ty(t), atoms=[self.ty_atom(p) for p in params])

    def _emit_with(self, name, eqs, ptys, rty, atoms=None):
        atoms = atoms or [f"({x})" if " " in x else x for x in ptys]
        pat_lists = []
        for eq in eqs:
            ps = eq.child_by_field_name("patterns")
            pat_lists.append(kids(ps) if ps is not None else [])
        arity = len(pat_lists[0])
        if any(len(p) != arity for p in pat_lists):
            self.fail(eqs[0], "equations with different numbers of parameters")
        for eq in eqs:
            if eq.child_by_field_name("match") is None:
                self.fail(eq, "equation without right-hand side")
        simple = len(eqs) == 1 and all(p.type == "variable" for p in pat_lists[0])
        typed = min(arity, len(ptys))
        if simple:
            names = [self.ident(self.text(p)) for p in pat_lists[0]]
        else:
            names = [f"x{i}" for i in range(arity)]
        binders = " ".join(f"({nm} : {ty})" for nm, ty in zip(names[:typed], ptys[:typed]))
        rest = atoms[typed:]
        result = " → ".join(list(rest) + [rty])
        extra = names[typed:]   # more parameters than the signature shows (result is a function synonym)
        head = f"def {self.ident(name)} {binders} : {result} :=".replace("  ", " ")
        out = [f"/-- Haskell `{name}` -/", head]
        lam = f"fun {' '.join(extra)} => " if extra else ""

        def body_of(eq, ind):
            lines = []
            wheres = eq.child_by_field_name("binds")
            if wheres is not None:
                for b in self.ordered_binds(kids(wheres)):
                    lb = self.local_bind(b, ind)
                    if lb:
                        lines.append(lb)
            lines.append(self.rhs(eq, ind, last=(eq == eqs[-1])))
            return ("\n" + " " * ind).join(lines)

        if simple:
            out.append("  " + lam + body_of(eqs[0], 2))
            return "\n".join(out)
        out.append(f"  {lam}match {', '.join(names)} with")
        for eq, pats in zip(eqs, pat_lists):
            b = body_of(eq, 6)
            if "\n" in b:
                b = "\n      " + b
            out.append(f"  | {', '.join(self.pat(p) for p in pats)} => {b}")
        return "\n".join(out)

    def free_names(self, node):
        """Variable names used under `node` (for ordering definitions)."""
        names = set()
        stack = [node]
        while stack:
            m = stack.pop()
            if m.type == "variable":
                names.add(self.text(m))
            stack.extend(kids(m))
        return names


def load_data(paths_and_types):
    data = DataInfo()
    for path, types in paths_and_types:
        src, root = parse_file(path)
        tr = Translator(src, data)
        for name, nodes in top_decls(src, root):
            if name in types:
                tr.collect_data(name, nodes[0])
    return data


HEADER = """/-
  GENERATED by tools/hs2lean from l4v {rev}: {path}
  SPDX-License-Identifier: GPL-2.0-only (derived from seL4/l4v, https://github.com/seL4/l4v)
  Do not edit by hand; regenerate with env/remote/hs2lean.sh.
-/
"""


def cmd_types(structures, types, rev):
    data = load_data([(structures, set(types))])
    src, root = parse_file(structures)
    tr = Translator(src, data)
    found = {name: nodes for name, nodes in top_decls(src, root) if name in types}
    missing = set(types) - set(found)
    if missing:
        raise Unsupported(f"types not found: {sorted(missing)}")
    print(HEADER.format(rev=rev, path=structures.split("/l4v/")[-1]))
    print("import Sel4Lean.Exec.Stubs\n\nnamespace Sel4Lean.Exec\n")
    for name in types:  # given order = dependency order
        print(tr.emit_data(name, found[name][0]))
        print()
    print("end Sel4Lean.Exec")


def cmd_module(module, structures, types, rev, imports):
    data = load_data([(structures, set(types))])
    src, root = parse_file(module)
    tr = Translator(src, data)
    decls = [(n, ns) for n, ns in top_decls(src, root) if any(d.type in ("function", "bind") for d in ns)]
    defined = {n for n, _ in decls}
    deps = {n: (set().union(*(tr.free_names(d) for d in ns if d.type != "signature")) & defined) - {n}
            for n, ns in decls}
    # topological order (Lean needs definitions before use)
    order, done = [], set()

    def visit(n, path=()):
        if n in done:
            return
        if n in path:
            raise Unsupported(f"recursive definitions: {' -> '.join(path + (n,))}")
        for d in sorted(deps[n]):
            visit(d, path + (n,))
        done.add(n)
        order.append(n)
    for n, _ in decls:
        visit(n)
    body = dict(decls)
    print(HEADER.format(rev=rev, path=module.split("/l4v/")[-1]))
    for i in imports:
        print(f"import {i}")
    print("\nnamespace Sel4Lean.Exec\nnoncomputable section\n")
    for n in order:
        print(tr.emit_function(n, body[n]))
        print()
    print("end\nend Sel4Lean.Exec")


if __name__ == "__main__":
    args = sys.argv[1:]
    rev = "unknown"
    if "--rev" in args:
        i = args.index("--rev"); rev = args[i + 1]; del args[i:i + 2]
    try:
        if args[0] == "types":
            cmd_types(args[1], args[2:], rev)
        elif args[0] == "module":
            mod = args[1]
            i = args.index("--types")
            structures, types = args[i + 1], args[i + 2:]
            j = args.index("--imports") if "--imports" in args else None
            imports = args[j + 1:i] if j else ["Sel4Lean.Exec.ThreadStubs"]
            cmd_module(mod, structures, types, rev, imports)
        else:
            raise SystemExit(__doc__)
    except Unsupported as ex:
        print(f"hs2lean: {ex}", file=sys.stderr)
        sys.exit(2)
