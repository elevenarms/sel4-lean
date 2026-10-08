"""l4v's design-spec skeletons (spec/design/skel/*.thy): which Haskell definitions the Isabelle executable
spec takes from the Haskell, and which it replaces with hand-written Isabelle.

l4v builds spec/design/*.thy from the skeletons with its own translator: each `#INCLUDE_HASKELL file opts`
line pulls in definitions of a Haskell module, filtered by `ONLY a b …` or `NOT a b …`, as declarations
(`decls_only`), bodies (`bodies_only`) or both. A name a module defines that no directive includes is not
in l4v's spec; when the skeleton (or l4v's machine theories) defines it by hand, the hand version is the spec.

    skel.py summary L4V_SPEC_DIR       per Haskell file: included / excluded names
    skel.py dropped L4V_SPEC_DIR HS_SRC
                                       every top-level Haskell definition l4v's spec does not take from the
                                       Haskell (dropped by NOT/ONLY, or its module not included at all)
"""
import os
import re
import sys

ARCH = "RISCV64"
DIRECTIVE = re.compile(r"^#INCLUDE_HASKELL(?:_PREPARSE)?\s+(\S+)(.*)$")
OPTION_WORDS = {"decls_only", "bodies_only", "instanceproofs", "ONLY", "NOT", "CONTEXT", "ArchInv=", "ArchLabels="}


def directives(spec_dir):
    """[(skeleton file, haskell path, mode, only set|None, not set)] for generic and RISCV64 skeletons."""
    out = []
    skel = os.path.join(spec_dir, "design", "skel")
    mskel = os.path.join(spec_dir, "design", "m-skel", ARCH)   # machine skeletons (MachineTypes.thy)
    files = [os.path.join(skel, f) for f in sorted(os.listdir(skel)) if f.endswith(".thy")]
    files += [os.path.join(skel, ARCH, f) for f in sorted(os.listdir(os.path.join(skel, ARCH))) if f.endswith(".thy")]
    files += [os.path.join(mskel, f) for f in sorted(os.listdir(mskel)) if f.endswith(".thy")]
    for path in files:
        # directives may continue over lines with a trailing backslash
        lines, buf = [], ""
        for raw in open(path, errors="replace"):
            buf += raw.rstrip("\n")
            if buf.endswith("\\"):
                buf = buf[:-1] + " "
                continue
            lines.append(buf); buf = ""
        for line in lines:
            m = DIRECTIVE.match(line.strip())
            if not m or "_PREPARSE" in line.split()[0]:
                continue
            if "instanceproofs" in line.split():
                continue   # only the instance proofs of the named types: no definitions
            hs, rest = m.group(1), m.group(2)
            toks = rest.split()
            mode = "decls_only" if "decls_only" in toks else "bodies_only" if "bodies_only" in toks else "all"
            only = nots = None
            if "ONLY" in toks:
                only = set(t for t in toks[toks.index("ONLY") + 1:] if t not in ("NOT",))
            if "NOT" in toks:
                nots = set(toks[toks.index("NOT") + 1:])
            out.append((os.path.relpath(path, os.path.dirname(skel)), hs.replace("TARGET", ARCH), mode, only,
                        nots or set()))
    return out


def included(spec_dir):
    """Haskell file -> (names included somewhere or None = 'all, minus exclusions', names excluded everywhere).

    A name is in l4v's spec if some directive for its file includes it (no ONLY list and not in its NOT
    list, or in its ONLY list). `excluded` lists names that every directive leaves out explicitly (NOT)."""
    per = {}
    for _, hs, _, only, nots in directives(spec_dir):
        per.setdefault(hs, []).append((only, nots))
    res = {}
    for hs, ds in per.items():
        def keeps(name, ds=ds):
            return any((only is None and name not in nots) or (only is not None and name in only)
                       for only, nots in ds)
        explicit_not = set.intersection(*[nots for only, nots in ds if only is None]) if any(
            only is None for only, _ in ds) else set()
        res[hs] = (keeps, explicit_not, ds)
    return res


def cmd_summary(spec_dir):
    inc = included(spec_dir)
    tot = 0
    for hs, (keeps, excl, ds) in sorted(inc.items()):
        onl = sum(1 for o, _ in ds if o is not None)
        print(f"{hs:55s} directives {len(ds)}  only-lists {onl}  excluded {len(excl)}: {' '.join(sorted(excl))[:110]}")
        tot += len(excl)
    print(f"skel: {len(inc)} Haskell files included, {tot} names excluded (replaced by hand-written Isabelle)")


def dropped(spec_dir, hs_src):
    """{haskell module path: [names l4v does not take from the Haskell]}, and the set of excluded modules."""
    from hs2lean import parse_file, top_decls
    import full
    inc = included(spec_dir)
    out, whole = {}, set()
    for hm, path in sorted(full.module_paths(hs_src).items()):
        rel = os.path.relpath(path, hs_src)
        src, rn = parse_file(path)
        names = [n for n, ns in top_decls(src, rn) if any(d.type in ("function", "bind") for d in ns)]
        if rel not in inc:
            whole.add(rel)
            out[rel] = names
            continue
        keeps = inc[rel][0]
        d = [n for n in names if not keeps(n)]
        if d:
            out[rel] = d
    return out, whole


def cmd_dropped(spec_dir, hs_src):
    out, whole = dropped(spec_dir, hs_src)
    for rel, names in out.items():
        tag = "MODULE NOT IN l4v SPEC" if rel in whole else "dropped"
        print(f"{rel}\t{tag}\t{len(names)}\t{' '.join(names)}")
    print(f"skel: {sum(len(v) for k, v in out.items() if k not in whole)} definitions dropped from included modules; "
          f"{len(whole)} modules not in l4v's spec ({sum(len(out[w]) for w in whole)} definitions)")


if __name__ == "__main__":
    if sys.argv[1] == "summary":
        cmd_summary(sys.argv[2])
    elif sys.argv[1] == "dropped":
        cmd_dropped(sys.argv[2], sys.argv[3])
    else:
        raise SystemExit(__doc__)
