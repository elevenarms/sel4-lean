"""W2 coverage sweep: run module mode on every RISCV64-relevant module of the Haskell spec.

    sweep.py ROOT_SRC_DIR OUT_TSV
Translation only (no Lean compile). Writes module, functions translated/total, external stubs, unresolved.
"""
import io
import os
import sys
import contextlib
import full

TYPE_ROOTS = ["SEL4/Object/Structures.lhs", "SEL4/Object/Structures/RISCV64.hs", "SEL4/Model/StateData.lhs",
              "SEL4/Model/StateData/RISCV64.hs", "SEL4/Model/PSpace.lhs"]


def main(root, out_tsv):
    mods = []
    for d, _, fs in os.walk(os.path.join(root, "SEL4")):
        for f in sorted(fs):
            p = os.path.join(d, f)
            if f.endswith((".hs", ".lhs")) and full.arch_ok(p) and not f.endswith("-boot"):
                mods.append(p)
    type_roots = [os.path.join(root, t) for t in TYPE_ROOTS] + mods   # every module's data types
    rows, tot_t, tot_n = [], 0, 0
    reasons = {}
    for m in sorted(mods):
        err = io.StringIO()
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(err):
            try:
                full.cmd_module(root, type_roots, [m])
            except Exception as ex:  # parser/translator crash: count as all failed
                print(f"hs2lean module: 0/0 functions translated, crash {type(ex).__name__}: {ex}", file=sys.stderr)
        lines = err.getvalue().splitlines()
        head = next((l for l in lines if l.startswith("hs2lean module:")), "hs2lean module: ?")
        try:
            frac = head.split(":")[1].split()[0]
            t, n = map(int, frac.split("/"))
        except Exception:
            t, n = 0, 0
        tot_t += t; tot_n += n
        for l in lines:
            if l.strip().startswith("failed "):
                why = l.split(":", 1)[1].strip().split(" at line")[0][:60]
                reasons[why] = reasons.get(why, 0) + 1
        rows.append((os.path.relpath(m, root), t, n, head.split("translated,")[-1].strip()))
    with open(out_tsv, "w") as f:
        f.write("module\ttranslated\ttotal\tnotes\n")
        for r in rows:
            f.write("\t".join(map(str, r)) + "\n")
        f.write(f"TOTAL\t{tot_t}\t{tot_n}\t{len(rows)} modules\n")
    print(f"coverage: {tot_t}/{tot_n} functions ({100 * tot_t / max(tot_n, 1):.1f}%) across {len(rows)} modules")
    print("top failure reasons:")
    for why, c in sorted(reasons.items(), key=lambda x: -x[1])[:15]:
        print(f"  {c:4d}  {why}")


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
