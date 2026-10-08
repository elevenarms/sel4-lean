"""W3 differential test: evaluate pure functions in l4v's Haskell model (GHC) and in the generated Lean.

    difftest.py gen ROOT_SRC STATUS OUTDIR [N]   writes OUTDIR/cases.tsv, OUTDIR/Test.ghci, OUTDIR/DiffTest.lean
    difftest.py compare OUTDIR                    reads OUTDIR/hs.out, OUTDIR/lean.out, writes OUTDIR/difftest.tsv

Only monomorphic functions/constants over word-like types are tested (inputs/outputs both sides can print).
Inputs come from a fixed seed: boundary values plus random ones.
"""
import os
import random
import re
import sys

from hs2lean import parse_file, top_decls
import full

# Haskell type -> (generator kind, Haskell input expr, Lean input expr, Haskell output conv, Lean output conv)
WORD_BITS = {"Word": 64, "Word64": 64, "Word32": 32, "Word16": 16, "Word8": 8,
             "Domain": 8, "Priority": 8, "DomainDuration": 64}
NEWTYPES = {"CPtr": ("CPtr", "fromCPtr", 64), "VPtr": ("VPtr", "fromVPtr", 64),
            "PAddr": ("PAddr", "fromPAddr", 64), "ASID": ("ASID", "fromASID", 64)}


def ty_info(t):
    t = t.strip()
    if t in WORD_BITS:
        n = WORD_BITS[t]
        lean_t = "Sel4Lean.Exec.Word" if n == 64 else f"BitVec {n}"
        return ("word", n,
                lambda v, t=t: f"({v} :: {t})", lambda v, lt=lean_t: f"({v} : {lt})",
                lambda e: f"toInteger ({e})", lambda e: f"({e}).toNat")
    if t == "Int":
        return ("nat", 64, lambda v: f"({v} :: Int)", lambda v: f"({v} : Nat)",
                lambda e: f"toInteger ({e})", lambda e: f"({e})")
    if t == "Bool":
        return ("bool", 1, lambda v: "True" if v else "False", lambda v: "true" if v else "false",
                lambda e: f"(if {e} then 1 else 0 :: Integer)", lambda e: f"(if {e} then 1 else 0)")
    if t in NEWTYPES:
        c, f, n = NEWTYPES[t]
        return ("word", n, lambda v, c=c: f"({c} {v})", lambda v, c=c: f"(Sel4Lean.Spec.{c}.{c} {v})",
                # unwrap by pattern: the selector name is ambiguous in GHCi (Hardware re-exports and redefines it)
                lambda e, c=c: f"(\\({c} w) -> toInteger w) ({e})", lambda e, f=f: f"({e}).{f}.toNat")
    m = re.fullmatch(r"PPtr\s+(\(?[A-Za-z0-9_ ]+\)?)", t)
    if m:
        # `PPtr a` (polymorphic pointee): instantiate a at the unit type on both sides
        poly = m.group(1)[:1].islower()
        hs_t, lean_t = ("PPtr ()", "Sel4Lean.Exec.PPtr Unit") if poly else (t, "Sel4Lean.Exec.PPtr _")
        return ("word", 64, lambda v: f"(PPtr {v} :: {hs_t})", lambda v: f"(Sel4Lean.Exec.PPtr.mk {v} : {lean_t})",
                lambda e: f"toInteger (fromPPtr ({e} :: {hs_t}))", lambda e: f"(({e} : {lean_t})).ptr.toNat")
    return None


def isabelle_values(outdir):
    """Case id -> value computed by l4v's Isabelle spec (isagate.py), if that gate has run."""
    p = os.path.join(outdir, "isabelle", "values.tsv")
    if not os.path.exists(p):
        return {}
    import isagate
    res = {}
    for line in open(p):
        parts = line.rstrip("\n").split("\t", 1)
        if len(parts) == 2 and isagate.parse_isa(parts[1]) is not None:
            res[int(parts[0])] = isagate.parse_isa(parts[1])
    return res


def values(kind, n, rnd, count):
    if kind == "bool":
        return [rnd.random() < 0.5 for _ in range(count)]
    if kind == "nat":   # sizes, shift amounts, indices
        base = [0, 1, 2, 3, 8, 12, 31, 32, 63]
        return (base + [rnd.randrange(0, 64) for _ in range(count)])[:count]
    top = (1 << n) - 1
    base = [v for v in [0, 1, 2, 7, 4095, 4096] if v <= top] + [top, 1 << (n - 1)]
    return (base + [rnd.randrange(0, top + 1) for _ in range(count)])[:count]


def exports(src, rn):
    """Names in the module's export list, or None if it exports everything."""
    hdr = next((c for c in rn.children if c.type == "header"), None)
    lst = hdr.child_by_field_name("exports") if hdr is not None else None
    if lst is None:
        return None
    return set(re.findall(r"[A-Za-z_][A-Za-z0-9_']*", src[lst.start_byte:lst.end_byte].decode()))


def candidates(root, status):
    ok = {l.split()[1] for l in open(status) if l.startswith("✔")}
    out = []
    for hm, path in sorted(full.module_paths(root).items()):
        lm = full.lean_module(hm)
        if lm not in ok or hm.split(".")[-1] in ("Init", "BootInfo"):
            continue
        src, rn = parse_file(path)
        exp = exports(src, rn)
        for name, nodes in top_decls(src, rn):
            if exp is not None and name not in exp:
                continue   # not exported: GHCi can't name it as Module.f
            sig = next((d for d in nodes if d.type == "signature"), None)
            if sig is None or not any(d.type in ("function", "bind") for d in nodes):
                continue
            tn = sig.child_by_field_name("type")
            if tn.type == "context":
                continue   # polymorphic (constrained) — not monomorphic
            t = src[tn.start_byte:tn.end_byte].decode().replace("\n", " ")
            parts = [p.strip() for p in t.split("->")]
            infos = [ty_info(p) for p in parts]
            if all(i is not None for i in infos):
                out.append((lm, hm, name, parts, infos))
    return out


def cmd_gen(root, status, outdir, n=8):
    rnd = random.Random(20261008)
    os.makedirs(outdir, exist_ok=True)
    cands = candidates(root, status)
    cases, hs_lines, lean_lines = [], [], []
    mods = sorted({c[1] for c in cands})
    hs_lines.append(":set -XScopedTypeVariables")
    hs_lines.append("import Prelude hiding (Word)")   # the spec's Word, as in its own modules
    hs_lines.append(":m + " + " ".join(mods + ["SEL4.Machine.RegisterSet", "SEL4.Model"]))
    imports = sorted({c[0] for c in cands})
    lean_lines += [f"import Sel4Lean.Spec.Gen.Mod.{m}" for m in imports]
    lean_lines.append("")
    cid = 0
    for lm, hm, name, parts, infos in cands:
        args, res = infos[:-1], infos[-1]
        rows = [()] if not args else list(zip(*[values(i[0], i[1], rnd, n) for i in args]))
        for row in rows:
            cid += 1
            hs_args = " ".join(i[2](v) for i, v in zip(args, row))
            lean_args = " ".join(i[3](v) for i, v in zip(args, row))
            hs_call = f"{hm}.{name} {hs_args}".strip()
            lean_call = f"Sel4Lean.Spec.M.{lm}.{full.Translator.ident(name)} {lean_args}".strip()
            hs_lines.append(f'putStrLn ("{cid}|" ++ show ({res[4]("(" + hs_call + ")")}))')
            lean_lines.append(f'#eval IO.println s!"{cid}|{{{res[5]("(" + lean_call + ")")}}}"')
            cases.append((cid, lm, name, " -> ".join(parts), " ".join(str(v) for v in row)))
    open(os.path.join(outdir, "Test.ghci"), "w").write("\n".join(hs_lines) + "\n:q\n")
    open(os.path.join(outdir, "DiffTest.lean"), "w").write("\n".join(lean_lines) + "\n")
    with open(os.path.join(outdir, "cases.tsv"), "w") as f:
        f.write("id\tmodule\tfunction\ttype\targs\n")
        for c in cases:
            f.write("\t".join(map(str, c)) + "\n")
    print(f"difftest: {len(cands)} functions, {len(cases)} cases")


def parse_out(path):
    """id -> value; "error" when the case started printing but raised (Haskell `error`/`undefined`)."""
    res = {}
    for line in open(path, errors="replace"):
        m = re.match(r"^(\d+)\|(-?\d+)\s*$", line.strip())
        if m:
            res[int(m.group(1))] = int(m.group(2))
        elif re.match(r"^\d+\|", line.strip()) and "Exception" in line:
            res.setdefault(int(line.split("|")[0]), "error")
    return res


def cmd_compare(outdir):
    cases = [l.rstrip("\n").split("\t") for l in open(os.path.join(outdir, "cases.tsv"))][1:]
    hs, ln = parse_out(os.path.join(outdir, "hs.out")), parse_out(os.path.join(outdir, "lean.out"))
    # where l4v's Isabelle spec replaces a Haskell definition, the Isabelle value is the reference: a
    # Lean/Haskell difference is fine exactly when Lean equals Isabelle (verdict `l4v`)
    isa = isabelle_values(outdir)
    stats, per_fn = {"agree": 0, "DIFFER": 0, "int-nat": 0, "hs-error": 0, "l4v": 0, "lean-missing": 0, "hs-missing": 0}, {}
    with open(os.path.join(outdir, "difftest.tsv"), "w") as f:
        f.write("id\tmodule\tfunction\targs\thaskell\tlean\tverdict\n")
        for cid, lm, name, ty, args in cases:
            i = int(cid)
            h, l = hs.get(i), ln.get(i)
            v = ("hs-missing" if h is None
                 # Haskell `error`: undefined there; the translation's `default` is a refinement (l4v: undefined)
                 else "hs-error" if h == "error" else "lean-missing" if l is None
                 else "agree" if h == l
                 else "l4v" if isa.get(i) == l
                 # Haskell Int is Nat in this model (as in l4v's translator): negative results truncate
                 else "int-nat" if h < 0 and l == 0 and "Int" in ty.split("->")[-1]
                 else "DIFFER")
            stats[v] += 1
            per_fn.setdefault((lm, name), []).append(v)
            f.write(f"{cid}\t{lm}\t{name}\t{args}\t{h}\t{l}\t{v}\n")
    print("difftest: " + ", ".join(f"{k} {v}" for k, v in stats.items()))
    for (lm, name), vs in sorted(per_fn.items()):
        if "DIFFER" in vs:
            print(f"  DIFFER  {lm}.{name}: {vs.count('DIFFER')}/{len(vs)} cases")
    fns = len(per_fn)
    ok = sum(1 for vs in per_fn.values() if all(v in ("agree", "int-nat", "hs-error", "l4v") for v in vs))
    print(f"difftest: {ok}/{fns} functions agree on every case (int-nat: negative Haskell Int; hs-error: Haskell `error`; l4v: Lean = l4v's Isabelle spec, which differs from the Haskell)")


if __name__ == "__main__":
    if sys.argv[1] == "gen":
        cmd_gen(sys.argv[2], sys.argv[3], sys.argv[4], int(sys.argv[5]) if len(sys.argv) > 5 else 8)
    elif sys.argv[1] == "compare":
        cmd_compare(sys.argv[2])
    else:
        raise SystemExit(__doc__)
