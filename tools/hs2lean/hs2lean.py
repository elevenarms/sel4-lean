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
}
# Haskell operator -> Lean operator (None: function application, handled specially)
OPERATOR = {
    "$": None, "||": "||", "&&": "&&", "==": "==", "/=": "!=", "<": "<", "<=": "≤", ">": ">", ">=": "≥",
    ":": "::", "++": "++", ".|.": "|||", ".&.": "&&&", "+": "+", "-": "-", "*": "*",
}
# Haskell names -> Lean names (Prelude.lean)
NAME = {
    "return": "pure", "fail": "failH", "assert": "assertH", "stateAssert": "stateAssertH",
    "forM_": "forM_H", "mapM_": "forM_H", "delete": "deleteH",
    "Just": "some", "Nothing": "none", "True": "true", "False": "false",
}
TYPE = {"Maybe": "Option", "Bool": "Bool", "Word": "Word", "Int": "Int", "Integer": "Int"}
LEAN_KEYWORDS = {"at", "by", "do", "else", "end", "for", "from", "fun", "have", "if", "in", "let",
                 "match", "open", "then", "with", "where", "show", "from", "λ", "Type", "Prop"}


class DataInfo:
    """Constructors and fields of the translated data types, used to resolve names."""

    def __init__(self):
        self.types = {}      # type -> {"ctors": [(ctor, [(field, type_node)] or None, [arg type nodes])], "single": bool}
        self.ctor_type = {}  # ctor -> type
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
                    fname = self.text(f.child_by_field_name("name"))
                    fields.append((fname, f.child_by_field_name("type")))
                ctors.append((cname, fields, [t for _, t in fields]))
            else:
                self.fail(c)
        info = {"ctors": ctors, "single": len(ctors) == 1 and ctors[0][1] is not None}
        self.data.types[name] = info
        for cname, fields, _ in ctors:
            self.data.ctor_type[cname] = name
            for fname, _ in fields or []:
                self.data.field_type[fname] = name

    def emit_data(self, name, node):
        info = self.data.types[name]
        derives = "deriving Inhabited"
        d = node.child_by_field_name("deriving")
        if d is not None and "Eq" in self.text(d):
            derives = "deriving Inhabited, DecidableEq"
        out = []
        if info["single"]:
            cname, fields, _ = info["ctors"][0]
            out.append(f"/-- Haskell `data {name} = {cname} {{ … }}` -/")
            out.append(f"structure {name} where")
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
        # Haskell field selectors and record update, per field (fields may be shared by constructors)
        fields_all = {}
        for cname, fields, args in info["ctors"]:
            for i, (fname, ft) in enumerate(fields or []):
                fields_all.setdefault(fname, (ft, []))[1].append((cname, i, len(fields)))
        for fname, (ft, owners) in fields_all.items():
            total = len(owners) == len(info["ctors"])
            fty = self.ty(ft)
            out.append("")
            out.append(f"/-- Haskell selector `{fname}` (partial in Haskell; `default` elsewhere, like Isabelle). -/")
            out.append(f"def {name}.{fname} : {name} → {fty}")
            for cname, i, n in owners:
                pats = " ".join("v" if j == i else "_" for j in range(n))
                out.append(f"  | .{cname} {pats} => v")
            if not total:
                out.append("  | _ => default")
            out.append(f"/-- Haskell record update `x {{ {fname} = v }}` (no-op on other constructors). -/")
            out.append(f"def {name}.set_{fname} (x : {name}) (v : {fty}) : {name} :=")
            out.append("  match x with")
            for cname, i, n in owners:
                pats = " ".join("_" if j == i else f"a{j}" for j in range(n))
                args = " ".join("v" if j == i else f"a{j}" for j in range(n))
                out.append(f"  | .{cname} {pats} => .{cname} {args}")
            if not total:
                out.append("  | x => x")
        return "\n".join(out)

    # ---------------- names

    def var(self, name):
        if name in NAME:
            return NAME[name]
        if name in self.data.field_type:
            return f"{self.data.field_type[name]}.{name}"
        return self.ident(name)

    def ctor(self, name):
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
            return " ".join([self.ctor(self.text(m))] + [self.pat_atom(p) for p in reversed(parts)])
        if t == "infix":
            op = self.text(n.child_by_field_name("operator"))
            if op != ":":
                self.fail(n, "pattern operator")
            return f"{self.pat_atom(n.child_by_field_name('left_operand'))} :: {self.pat(n.child_by_field_name('right_operand'))}"
        if t == "record":
            # `C {}` matches any C, whatever its fields
            c = n.child_by_field_name("constructor")
            if c is None or any(x.type == "field_pattern" for x in kids(n)):
                self.fail(n, "record pattern with fields")
            return f"{self.ctor(self.text(c))} .."
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
        for o, name in zip(ops, names):
            if name not in FIXITY or (name not in OPERATOR):
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
        if op == "$":
            left = self.e(l[1], ind) if l[0] == "leaf" and l[1].type in ("apply", "variable", "constructor") else self.render_atom(l, ind)
            return f"{left} {self.render_atom(r, ind)}"
        return f"{self.render_atom(l, ind)} {OPERATOR[op]} {self.render_atom(r, ind)}"

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
            fname = self.text(f.child_by_field_name("field"))
            upd.append((fname, f.child_by_field_name("expression")))
        if ctor is not None and base is None:
            # construction: C { f = v, ... } -> positional
            cname = self.text(ctor)
            tname = self.data.ctor_type.get(cname)
            if tname is None:
                self.fail(n, "record construction of unknown constructor")
            cfields = next(fs for c, fs, _ in self.data.types[tname]["ctors"] if c == cname)
            given = dict(upd)
            if set(given) != {f for f, _ in cfields}:
                self.fail(n, "record construction must give every field")
            if self.data.types[tname]["single"]:
                return "{ " + ", ".join(f"{f} := {self.e(given[f], ind + 2)}" for f, _ in cfields) + f" : {tname} }}"
            return " ".join([self.ctor(cname)] + [self.atom(given[f], ind) for f, _ in cfields])
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

    def do(self, n, ind):
        stmts = [c for c in kids(n) if c.type in ("bind", "exp", "let")]
        if len(stmts) != len(kids(n)):
            bad = next(c for c in kids(n) if c not in stmts)
            self.fail(bad, "do statement")
        lines = []
        si = ind + 2
        for s in stmts:
            if s.type == "bind":
                p = self.pat(s.child_by_field_name("pattern"))
                lines.append(f"let {p} ← {self.e(s.child_by_field_name('expression'), si + 2)}")
            elif s.type == "exp":
                lines.append(self.e(kids(s)[0], si))
            else:
                for b in kids(s.child_by_field_name("binds")):
                    lines.append(self.local_bind(b, si))
        pad = " " * si
        return "do\n" + "\n".join(pad + l for l in lines)

    def local_bind(self, b, ind):
        if b.type == "bind":
            name = self.ident(self.text(b.child_by_field_name("name")))
            body = b.child_by_field_name("match").child_by_field_name("expression")
            return f"let {name} := {self.e(body, ind + 2)}"
        if b.type == "function":
            name = self.ident(self.text(b.child_by_field_name("name")))
            ps = kids(b.child_by_field_name("patterns"))
            body = b.child_by_field_name("match").child_by_field_name("expression")
            return f"let {name} := fun {' '.join(self.pat_atom(p) for p in ps)} => {self.e(body, ind + 2)}"
        self.fail(b, "local binding")

    def case(self, n, ind):
        scrut = next(c for c in kids(n) if c.type != "alternatives")
        alts = n.child_by_field_name("alternatives")
        lines = [f"match {self.e(scrut, ind + 2)} with"]
        for a in kids(alts):
            p = self.pat(a.child_by_field_name("pattern"))
            m = a.child_by_field_name("match")
            if m.child_by_field_name("guards") is not None or any(c.type == "guards" for c in kids(m)):
                self.fail(a, "guarded alternative")
            body = m.child_by_field_name("expression")
            b = self.e(body, ind + 4)
            if body.type in ("case", "do", "conditional", "lambda"):
                b = f"({b})"
            lines.append(f"{' ' * ind}| {p} => {b}")
        return "\n".join(lines)

    # ---------------- functions

    def emit_function(self, name, nodes):
        sig = next((d for d in nodes if d.type == "signature"), None)
        eqs = [d for d in nodes if d.type in ("function", "bind")]
        if sig is None or len(eqs) != 1:
            self.fail(nodes[0], "function needs one signature and one equation")
        eq = eqs[0]
        # split the signature type into parameter types and result
        params, t = [], sig.child_by_field_name("type")
        while t.type == "function":
            params.append(t.child_by_field_name("parameter"))
            t = t.child_by_field_name("result")
        pats = eq.child_by_field_name("patterns")
        pats = kids(pats) if pats is not None else []
        if any(p.type != "variable" for p in pats):
            self.fail(eq, "non-variable parameter pattern")
        if len(pats) > len(params):
            self.fail(eq, "more parameters than the signature")
        binders = " ".join(f"({self.ident(self.text(p))} : {self.ty(ty)})" for p, ty in zip(pats, params))
        rest = params[len(pats):]
        result = " → ".join([self.ty_atom(x) for x in rest] + [self.ty(t)])
        m = eq.child_by_field_name("match")
        body = m.child_by_field_name("expression")
        wheres = eq.child_by_field_name("binds")
        out = [f"/-- Haskell `{name}` -/", f"def {self.ident(name)} {binders} : {result} :=".replace("  ", " ")]
        if wheres is not None:
            for b in kids(wheres):
                out.append("  " + self.local_bind(b, 2))
        out.append("  " + self.e(body, 2))
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
