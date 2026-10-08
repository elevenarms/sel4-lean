"""Lean <-> Isabelle value gate over *structured* values: pure spec functions whose arguments are datatypes
(capabilities, objects, enumerations, options, pairs, …), evaluated by l4v's Isabelle (ExecSpec) and by Lean.

    isagate2.py gen W3DIR CONSTS GEN_DIR [N]   writes W3DIR/isa2/{cases.tsv, Values2.thy, Gate2.lean}
    isagate2.py compare W3DIR                  compares W3DIR/isa2/{isabelle.tsv, lean.out}

Values are generated from the Lean constructors (parsed from Gen/Types.lean) and rendered twice: as a Lean
term, and as an Isabelle term using full constant names (a Haskell newtype is a type synonym in Isabelle
unless l4v keeps its constructor, which the constant table tells us). Results are compared as
S-expressions: `(Ctor arg …)`, decimal numbers, True/False, None/(Some x), (Pair a b), lists.
"""
import os
import random
import re
import sys

import isagate

BASE_TYPES = {"Word": 64, "RISCV64.Word": 64}


def split_top(s, sep):
    """Split s at sep outside brackets."""
    out, depth, cur, i = [], 0, "", 0
    while i < len(s):
        c = s[i]
        if c in "([{⟨":
            depth += 1
        elif c in ")]}⟩":
            depth -= 1
        if depth == 0 and s.startswith(sep, i):
            out.append(cur.strip()); cur = ""; i += len(sep); continue
        cur += c; i += 1
    out.append(cur.strip())
    return out


def strip_parens(t):
    t = t.strip()
    while t.startswith("(") and t.endswith(")"):
        depth = 0
        for i, c in enumerate(t):
            depth += c == "("
            depth -= c == ")"
            if depth == 0 and i < len(t) - 1:
                return t
        t = t[1:-1].strip()
    return t


def parse_types(path):
    """{lean type name: ("abbrev", target) | ("data", [(ctor, [field types])]) | ("struct", ctor, [field types])}"""
    types, lines = {}, open(path).read().split("\n")
    i = 0
    while i < len(lines):
        l = lines[i]
        m = re.match(r"^abbrev (\S+) := (.+)$", l)
        if m and "(" not in m.group(1):
            types[m.group(1)] = ("abbrev", m.group(2).strip())
        m = re.match(r"^inductive (\S+) where$", l)
        if m:
            name, ctors = m.group(1), []
            i += 1
            while i < len(lines) and lines[i].startswith("  |"):
                cl = lines[i][3:].strip()
                cname = cl.split()[0]
                fields = [f.split(" : ", 1)[1] for f in re.findall(r"\(([^()]*(?:\([^()]*\)[^()]*)*)\)", cl[len(cname):])
                          if " : " in f]
                ctors.append((cname, fields))
                i += 1
            types[name] = ("data", ctors)
            continue
        m = re.match(r"^structure (\S+) where$", l)
        if m:
            name = m.group(1)
            i += 1
            cm = re.match(r"^  (\S+) ::$", lines[i]) if i < len(lines) else None
            if cm:
                ctor, fields = cm.group(1), []
                i += 1
                while i < len(lines) and re.match(r"^  \w+ : ", lines[i]):
                    fields.append(lines[i].split(" : ", 1)[1].split(" := ")[0].strip())
                    i += 1
                types[name] = ("struct", ctor, fields)
            continue
        i += 1
    return types


def snake(lean_type):
    base = lean_type.split(".")[-1]
    return re.sub(r"(?<=[a-z0-9])(?=[A-Z])", "_", base).lower()


class Gen:
    def __init__(self, types, consts, rnd):
        self.types, self.rnd = types, rnd
        # Isabelle constructor constants: (base name, result type name) -> full name
        self.isa_ctor = {}
        for name, _, ty in consts:
            res = ty.split("\\<Rightarrow>")[-1].strip().split()[-1] if ty else ""
            self.isa_ctor.setdefault((name.split(".")[-1], res), name)

    def norm(self, t):
        t = strip_parens(t)
        t = re.sub(r"(_root_\.)?Sel4Lean\.Spec\.", "", t)
        seen = 0
        while t in self.types and self.types[t][0] == "abbrev" and seen < 10:
            t = strip_parens(self.types[t][1]); seen += 1
        return t

    def ctor_const(self, lean_type, ctor):
        return self.isa_ctor.get((ctor, snake(lean_type)))

    def value(self, t, depth=0):
        """An abstract value of Lean type t, or None if t is not generatable."""
        t = self.norm(t)
        r = self.rnd
        if t in BASE_TYPES or t.startswith("BitVec "):
            n = BASE_TYPES.get(t) or int(t.split()[1])
            top = (1 << n) - 1
            return ("num", r.choice([0, 1, 2, 7, top, 1 << (n - 1), r.randrange(0, top + 1)]) & top)
        if t == "Nat":
            return ("num", r.choice([0, 1, 2, 3, 5, 8, 12, 31, 63]))
        if t == "Bool":
            return ("bool", r.random() < 0.5)
        if t.startswith("PPtr ") or t.startswith("Sel4Lean.Exec.PPtr "):
            return ("ptr", r.choice([0, 0x1000, 0xFFFFFFC000001000, r.randrange(0, 1 << 64)]))
        if t.startswith("Option "):
            if depth > 3 or r.random() < 0.35:
                return ("none",)
            v = self.value(t[len("Option "):], depth + 1)
            return None if v is None else ("some", v)
        if t.startswith("List "):
            if depth > 3 or r.random() < 0.5:
                return ("list", [])
            v = self.value(t[len("List "):], depth + 1)
            return None if v is None else ("list", [v])
        parts = split_top(t, "×")
        if len(parts) == 2:
            a, b = self.value(parts[0], depth + 1), self.value(parts[1], depth + 1)
            return None if a is None or b is None else ("pair", a, b)
        if "→" in t or "Prop" in t:
            return None
        info = self.types.get(t)
        if info is None or depth > 4:
            return None
        if info[0] == "struct":
            _, ctor, fields = info
            args = [self.value(f, depth + 1) for f in fields]
            if any(a is None for a in args):
                return None
            transparent = len(fields) == 1 and self.ctor_const(t, ctor) is None
            return ("newtype", t, ctor, args[0]) if transparent else ("ctor", t, ctor, args)
        ctors = list(info[1])
        r.shuffle(ctors)
        ctors.sort(key=lambda c: len(c[1]) if depth > 2 else 0)
        for ctor, fields in ctors:
            args = [self.value(f, depth + 1) for f in fields]
            if all(a is not None for a in args):
                return ("ctor", t, ctor, args)
        return None

    def generatable(self, t, depth=0, seen=None):
        seen = set() if seen is None else seen
        t = self.norm(t)
        if t in BASE_TYPES or t.startswith("BitVec ") or t in ("Nat", "Bool"):
            return True
        if t.startswith("PPtr ") or t.startswith("Sel4Lean.Exec.PPtr "):
            return True
        for p in ("Option ", "List "):
            if t.startswith(p):
                return self.generatable(t[len(p):], depth + 1, seen)
        parts = split_top(t, "×")
        if len(parts) == 2:
            return all(self.generatable(p, depth + 1, seen) for p in parts)
        if "→" in t or t not in self.types or self.types[t][0] == "abbrev":
            return False
        if t in seen:
            return True
        seen = seen | {t}
        info = self.types[t]
        if info[0] == "struct":
            return all(self.generatable(f, depth + 1, seen) for f in info[2]) and (
                len(info[2]) == 1 or self.ctor_const(t, info[1]) is not None)
        return any(all(self.generatable(f, depth + 1, seen) for f in fs) for _, fs in info[1]) and all(
            self.ctor_const(t, c) is not None for c, _ in info[1])


def lean_type(t):
    """A normalised type, fully qualified for use outside the spec namespace."""
    out = []
    for tok in re.findall(r"[\w.]+|[^\w.]", t):
        if tok in ("Word", "RISCV64.Word"):
            out.append("(BitVec 64)")
        elif tok == "PPtr":
            out.append("Sel4Lean.Exec.PPtr")
        elif re.match(r"^[A-Z][\w.]*$", tok) and tok not in ("Option", "List", "Nat", "Bool", "BitVec", "Unit"):
            out.append("_root_.Sel4Lean.Spec." + tok)
        else:
            out.append(tok)
    return "".join(out)


def lean_term(v):
    k = v[0]
    if k == "num":
        return str(v[1])
    if k == "bool":
        return "true" if v[1] else "false"
    if k == "ptr":
        return f"⟨{v[1]}⟩"
    if k == "none":
        return "none"
    if k == "some":
        return f"(some {lean_term(v[1])})"
    if k == "pair":
        return f"({lean_term(v[1])}, {lean_term(v[2])})"
    if k == "list":
        return "[" + ", ".join(lean_term(x) for x in v[1]) + "]"
    if k == "newtype":
        return f"(_root_.Sel4Lean.Spec.{v[1]}.{v[2]} {lean_term(v[3])})"
    _, t, ctor, args = v
    return f"(_root_.Sel4Lean.Spec.{t}.{ctor}" + "".join(" " + lean_term(a) for a in args) + ")"


def isa_type(t, gen):
    """The Isabelle type for a (normalised) Lean type, or None when unknown."""
    t = gen.norm(t)
    if t in BASE_TYPES:
        return "64 word"
    if t.startswith("BitVec "):
        return f"{t.split()[1]} word"
    if t == "Nat":
        return "nat"
    if t == "Bool":
        return "bool"
    if t.startswith("PPtr ") or t.startswith("Sel4Lean.Exec.PPtr "):
        return "64 word"
    for p, q in (("Option ", "option"), ("List ", "list")):
        if t.startswith(p):
            inner = isa_type(t[len(p):], gen)
            return f"({inner}) {q}" if inner else None
    parts = split_top(t, "×")
    if len(parts) == 2:
        a, b = isa_type(parts[0], gen), isa_type(parts[1], gen)
        return f"({a} \\<times> {b})" if a and b else None
    info = gen.types.get(t)
    if info and info[0] == "struct" and len(info[2]) == 1 and gen.ctor_const(t, info[1]) is None:
        return isa_type(info[2][0], gen)   # a Haskell newtype: a type synonym in Isabelle
    return snake(t) if info else None


def isa_term(v, gen, ty=None):
    k = v[0]
    if k in ("num", "ptr"):
        it = isa_type(ty, gen) if ty else None
        return f"({v[1]} :: {it})" if it else str(v[1])
    if k == "bool":
        return "True" if v[1] else "False"
    if k == "none":
        return "None"
    inner_t = lambda i: None
    if ty:
        nt = gen.norm(ty)
        if nt.startswith("Option ") or nt.startswith("List "):
            inner_t = lambda i, nt=nt: nt.split(" ", 1)[1]
        elif len(split_top(nt, "×")) == 2:
            inner_t = lambda i, nt=nt: split_top(nt, "×")[i]
    if k == "some":
        return f"(Some {isa_term(v[1], gen, inner_t(0))})"
    if k == "pair":
        return f"({isa_term(v[1], gen, inner_t(0))}, {isa_term(v[2], gen, inner_t(1))})"
    if k == "list":
        return "[" + ", ".join(isa_term(x, gen, inner_t(0)) for x in v[1]) + "]"
    if k == "newtype":
        info = gen.types.get(v[1])
        return isa_term(v[3], gen, info[2][0] if info else None)
    _, t, ctor, args = v
    info = gen.types.get(t)
    ftys = (info[2] if info[0] == "struct" else dict(info[1]).get(ctor, [])) if info else []
    return f"({gen.ctor_const(t, ctor)}" + "".join(
        " " + isa_term(a, gen, ftys[i] if i < len(ftys) else None) for i, a in enumerate(args)) + ")"


def lean_sig(line):
    """`def f (x : A) (y : B) : R :=` -> (name, [A, B], R); point-free `def f : A → B :=` too."""
    m = re.match(r"^(?:partial )?def (\S+) (.*):=\s*$", line)
    if not m or "{" in m.group(2) or "[" in m.group(2):
        return None
    name, rest = m.group(1), m.group(2).strip()
    params = []
    while rest.startswith("("):
        depth = 0
        for i, c in enumerate(rest):
            depth += c == "("
            depth -= c == ")"
            if depth == 0:
                break
        grp = rest[1:i]
        if " : " not in grp:
            return None
        params.append(grp.split(" : ", 1)[1].strip())
        rest = rest[i + 1:].strip()
    if not rest.startswith(": "):
        return None
    fty = split_top(rest[2:].strip(), "→")
    return name, params + fty[:-1], fty[-1]


MONADS = ("Kernel", "KernelF", "KernelP", "MachineMonad", "UserMonad", "NondetM", "KernelInit", "StateT",
          "ExceptT", "IO", "Serializer", "ReaderT")


def cmd_gen(w3, consts_path, gen_dir, n=6):
    rnd = random.Random(20261008)
    consts = isagate.load_consts(consts_path)
    types = parse_types(os.path.join(gen_dir, "..", "Types.lean"))
    g = Gen(types, consts, rnd)
    status = os.path.join(w3, "..", "w2", "compile-status.txt")
    ok = {l.split()[1] for l in open(status) if l.startswith("✔")}
    out = os.path.join(w3, "isa2")
    os.makedirs(out, exist_ok=True)
    cases, lean_lines, isa_rows, result_types = [], [], [], set()
    funcs = 0
    for f in sorted(os.listdir(gen_dir)):
        mod = f[:-5]
        if not f.endswith(".lean") or mod not in ok:
            continue
        for line in open(os.path.join(gen_dir, f)):
            sig = lean_sig(line.rstrip("\n"))
            if sig is None:
                continue
            name, args, res = sig
            if any(re.search(rf"\b{mm}\b", t) for t in args + [res] for mm in MONADS):
                continue
            if not args:
                continue   # constants are covered by the word gate
            if not all(g.generatable(a) for a in args) or not g.generatable(res):
                continue
            c = isagate.resolve(mod, name, consts)
            if c is None:
                continue
            funcs += 1
            result_types.add(g.norm(res))
            for _ in range(n):
                vals = [g.value(a) for a in args]
                if any(v is None for v in vals):
                    continue
                cid = len(cases) + 1
                lean_call = f"Sel4Lean.Spec.M.{mod}.{name}" + "".join(" " + lean_term(v) for v in vals)
                lean_lines.append(f'#eval IO.println s!"{cid}|{{showS ({lean_call})}}"')
                call = c + "".join(" " + isa_term(v, g, a) for v, a in zip(vals, args))
                rt = isa_type(res, g)
                isa_rows.append((cid, f"({call} :: {rt})" if rt else call))
                cases.append((cid, mod, name, " ".join(lean_term(v) for v in vals)))
    # printers for result types (and everything they contain)
    printers = PrinterGen(g).emit(result_types)
    imports = sorted({c[1] for c in cases})
    with open(os.path.join(out, "Gate2.lean"), "w") as fh:
        fh.write("import Sel4Lean\n" + "".join(f"import Sel4Lean.Spec.Gen.Mod.{m}\n" for m in imports))
        fh.write("open Sel4Lean.Spec\nset_option maxRecDepth 4000\n\n" + printers + "\n\n" + "\n".join(lean_lines) + "\n")
    with open(os.path.join(out, "cases.tsv"), "w") as fh:
        fh.write("id\tmodule\tfunction\targs\n")
        for c in cases:
            fh.write("\t".join(map(str, c)) + "\n")
    # one line per case for the chunked evaluator (env/remote/isagate/Eval2.ML)
    with open(os.path.join(out, "isa-cases.tsv"), "w") as fh:
        for cid, t in isa_rows:
            fh.write(f"{cid}\t{t.replace(chr(92) + chr(92), chr(92))}\n")
    print(f"isagate2: {funcs} functions, {len(cases)} cases")


class PrinterGen:
    """`showS` for every type reachable from the result types, printing the S-expression form."""

    def __init__(self, g):
        self.g, self.done, self.defs = g, set(), []

    def ref(self, t):
        t = self.g.norm(t)
        if t in BASE_TYPES or t.startswith("BitVec "):
            n = BASE_TYPES.get(t) or int(t.split()[1])
            return f"(fun (x : BitVec {n}) => toString x.toNat)"
        if t == "Nat":
            return "(fun (x : Nat) => toString x)"
        if t == "Bool":
            return "(fun (x : Bool) => if x then \"True\" else \"False\")"
        if t.startswith("PPtr ") or t.startswith("Sel4Lean.Exec.PPtr "):
            return f"(fun (x : {lean_type(t)}) => toString x.ptr.toNat)"
        if t.startswith("Option "):
            inner = self.ref(t[len("Option "):])
            return f"(fun (x : {lean_type(t)}) => match x with | none => \"None\" | some v => \"(Some \" ++ {inner} v ++ \")\")"
        if t.startswith("List "):
            inner = self.ref(t[len("List "):])
            return f"(fun (xs : {lean_type(t)}) => \"[\" ++ \", \".intercalate (xs.map {inner}) ++ \"]\")"
        parts = split_top(t, "×")
        if len(parts) == 2:
            return f"(fun (p : {lean_type(t)}) => \"(Pair \" ++ {self.ref(parts[0])} p.1 ++ \" \" ++ {self.ref(parts[1])} p.2 ++ \")\")"
        fn = "show_" + re.sub(r"\W", "_", t)
        if t not in self.done:
            self.done.add(t)
            info = self.g.types[t]
            q = f"_root_.Sel4Lean.Spec.{t}"
            if info[0] == "struct":
                _, ctor, fields = info
                transparent = len(fields) == 1 and self.g.ctor_const(t, ctor) is None
                body = (f"  | .{ctor} a0 => {self.ref(fields[0])} a0" if transparent else
                        f"  | .{ctor}" + "".join(f" a{i}" for i in range(len(fields))) + f" => \"({ctor}\"" +
                        "".join(f" ++ \" \" ++ {self.ref(fl)} a{i}" for i, fl in enumerate(fields)) + " ++ \")\"")
                self.defs.append(f"partial def {fn} : {q} → String\n{body}")
            else:
                alts = []
                for ctor, fields in info[1]:
                    if not fields:
                        alts.append(f"  | .{ctor} => \"{ctor}\"")
                    else:
                        alts.append(f"  | .{ctor}" + "".join(f" a{i}" for i in range(len(fields))) + f" => \"({ctor}\"" +
                                    "".join(f" ++ \" \" ++ {self.ref(fl)} a{i}" for i, fl in enumerate(fields)) + " ++ \")\"")
                self.defs.append(f"partial def {fn} : {q} → String\n" + "\n".join(alts))
        return fn

    def emit(self, result_types):
        tops = {t: self.ref(t) for t in sorted(result_types)}
        cls = ("class ShowS (α : Type) where\n  showS : α → String\nexport ShowS (showS)\n")
        inst = "\n".join(f"instance : ShowS ({lean_type(t)}) := ⟨{r}⟩" for t, r in tops.items())
        return cls + "mutual\n" + "\n\n".join(self.defs) + "\nend\n" + inst if self.defs else cls + inst


VALUES2_THY = r'''theory Values2
  imports ExecSpec.API_H ExecSpec.ArchIntermediate_H
begin

text \<open>Evaluate spec functions on structured arguments in l4v's executable spec (generated by
tools/hs2lean/isagate2.py); print results as S-expressions. Output: GATE_OUT/isabelle2.tsv\<close>

ML \<open>
  val out = Path.explode (getenv "GATE_OUT") + Path.basic "isabelle2.tsv"
  val ctxt = @{context}
  val thy = @{theory}
  val space = Consts.space_of (Sign.consts_of thy)
  fun spec_const c = String.isPrefix "ExecSpec." (#theory_long_name (Name_Space.the_entry space c))
                     handle ERROR _ => false
  val def_tab =
    fold (fn (_, th) => fn tab =>
        (case Thm.prop_of th of
          Const (@{const_name Pure.eq}, _) $ lhs $ _ =>
            (case head_of lhs of
              Const (c, _) => if spec_const c then Symtab.cons_list (c, th) tab else tab
            | _ => tab)
        | _ => tab))
      (Thm.all_axioms_of thy) Symtab.empty
  fun consts_in t = Term.fold_aterms (fn Const (c, _) => insert (op =) c | _ => I) t []
  fun unfold t n =
    let val defs = maps (Symtab.lookup_list def_tab) (consts_in t) in
      if null defs orelse n = 0 then t
      else
        let val t' = Thm.rhs_of (Simplifier.rewrite (put_simpset HOL_basic_ss ctxt addsimps defs)
                                   (Thm.cterm_of ctxt t)) |> Thm.term_of
        in if t' aconv t then t else unfold t' (n - 1) end
    end
  val value = Timeout.apply (Time.fromSeconds 30) (Value_Command.value ctxt)
  fun simp u = Thm.rhs_of (Timeout.apply (Time.fromSeconds 30)
                 (Simplifier.rewrite (ctxt addsimps @{thms word_size})) (Thm.cterm_of ctxt u)) |> Thm.term_of
  fun base c = Long_Name.base_name c
  fun sexp t =
    (case try HOLogic.dest_number t of
      SOME (_, n) => string_of_int n
    | NONE =>
      (case strip_comb t of
        (Const (@{const_name True}, _), []) => "True"
      | (Const (@{const_name False}, _), []) => "False"
      | (Const (@{const_name None}, _), []) => "None"
      | (Const (@{const_name Nil}, _), []) => "[]"
      | (Const (@{const_name Cons}, _), _) =>
          (case try HOLogic.dest_list t of
            SOME xs => "[" ^ space_implode ", " (map sexp xs) ^ "]"
          | NONE => raise TERM ("open list", [t]))
      | (Const (@{const_name Pair}, _), [a, b]) => "(Pair " ^ sexp a ^ " " ^ sexp b ^ ")"
      | (Const (c, _), []) => base c
      | (Const (c, _), args) => "(" ^ base c ^ " " ^ space_implode " " (map sexp args) ^ ")"
      | _ => raise TERM ("not a value", [t])))
  fun eval1 s =
    let val t = Syntax.read_term ctxt s in
      (case Exn.result value t of
        Exn.Res v => sexp v
      | Exn.Exn _ =>
          let val u = unfold t 12 in
            (case Exn.result value u of
              Exn.Res v => sexp v
            | Exn.Exn _ => sexp (value (simp u)))
          end)
    end
  fun ev (id, s) =
    (case Exn.result (Timeout.apply (Time.fromSeconds 40) eval1) s of
      Exn.Res r => id ^ "\t" ^ r
    | Exn.Exn e => id ^ "\tERR " ^ hd (split_lines (Runtime.exn_message e) @ [""]))
  val cases = [
   @@CASES@@]
  (* cases are independent: evaluate them in parallel, in batches (bounded memory: the 32-bit Poly/ML heap
     runs out with all of them at once), appending each batch's results as it finishes *)
  val _ = File.write out ""
  fun batches [] = ()
    | batches xs = (File.append out (cat_lines (Par_List.map ev (take 8 xs)) ^ "\n"); batches (drop 8 xs))
  val _ = batches cases
  val _ = writeln ("GATE values2: " ^ string_of_int (length cases))
\<close>

end
'''


def cmd_compare(w3):
    out = os.path.join(w3, "isa2")
    cases = [l.rstrip("\n").split("\t") for l in open(os.path.join(out, "cases.tsv"))][1:]
    isa = {}
    for line in open(os.path.join(out, "isabelle2.tsv")):
        p = line.rstrip("\n").split("\t", 1)
        if len(p) == 2:
            isa[p[0]] = p[1]
    lean = {}
    for line in open(os.path.join(out, "lean.out"), errors="replace"):
        m = re.match(r"^(\d+)\|(.*)$", line.rstrip("\n"))
        if m:
            lean[m.group(1)] = m.group(2)
    stats, per_fn = {}, {}
    with open(os.path.join(out, "compare.tsv"), "w") as fh:
        fh.write("id\tmodule\tfunction\targs\tisabelle\tlean\tverdict\n")
        for cid, mod, fn, args in cases:
            i, l = isa.get(cid), lean.get(cid)
            if i is None or i.startswith("ERR"):
                v = "both-undefined" if i and "undefined" in i else "isabelle-unevaluated"
            elif l is None:
                v = "lean-missing"
            else:
                v = "agree" if norm(i) == norm(l) else "DIFFER"
            stats[v] = stats.get(v, 0) + 1
            per_fn.setdefault(f"{mod}.{fn}", []).append(v)
            fh.write(f"{cid}\t{mod}\t{fn}\t{args}\t{i}\t{l}\t{v}\n")
    print("isagate2: " + ", ".join(f"{k} {v}" for k, v in sorted(stats.items())))
    for fn, vs in sorted(per_fn.items()):
        bad = [v for v in vs if v not in ("agree", "both-undefined")]
        if bad:
            print(f"  {fn}: {len(bad)}/{len(vs)} {sorted(set(bad))}")
    ok = sum(1 for vs in per_fn.values() if all(v in ("agree", "both-undefined") for v in vs))
    print(f"isagate2: {ok}/{len(per_fn)} functions agree with Isabelle on every case")


def norm(s):
    s = re.sub(r"\s+", " ", s.strip())
    # Isabelle's simplifier may leave nat numerals as Suc chains: (Suc 0) = 1, (Suc 1) = 2, …
    prev = None
    while prev != s:
        prev = s
        s = re.sub(r"\(Suc (\d+)\)", lambda m: str(int(m.group(1)) + 1), s)
    return s


if __name__ == "__main__":
    if sys.argv[1] == "gen":
        cmd_gen(sys.argv[2], sys.argv[3], sys.argv[4], int(sys.argv[5]) if len(sys.argv) > 5 else 6)
    elif sys.argv[1] == "compare":
        cmd_compare(sys.argv[2])
    else:
        raise SystemExit(__doc__)
