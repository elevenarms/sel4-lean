"""List pure Haskell functions whose signatures use only simple types (W3 differential testing)."""
import os, re, sys
from hs2lean import parse_file, top_decls, kids
import full

SIMPLE = {"Word", "Int", "Bool", "Word8", "Word16", "Word32", "Word64", "Integer"}

def main(root, status):
    ok = {l.split()[1] for l in open(status) if l.startswith("✔")}
    for hm, path in sorted(full.module_paths(root).items()):
        lm = full.lean_module(hm)
        if lm not in ok:
            continue
        src, rn = parse_file(path)
        for name, nodes in top_decls(src, rn):
            sig = next((d for d in nodes if d.type == "signature"), None)
            if sig is None or not any(d.type in ("function", "bind") for d in nodes):
                continue
            t = src[sig.child_by_field_name("type").start_byte:sig.child_by_field_name("type").end_byte].decode()
            parts = [p.strip() for p in t.replace("\n", " ").split("->")]
            if all(p in SIMPLE for p in parts) and len(parts) >= 2:
                print(f"{lm}\t{hm}\t{name}\t{' -> '.join(parts)}")

if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
