# Notices

sel4-lean ports seL4's formal verification ([l4v](https://github.com/seL4/l4v)) to Lean 4. It derives from,
and its tests run against, the following work.

| Source | License | Used for |
|---|---|---|
| [seL4/l4v](https://github.com/seL4/l4v) `spec/haskell` (Haskell executable model) | GPL-2.0-only | input to the generated Lean in `lean/Sel4Lean/Spec/Gen`, `lean/Sel4Lean/Exec/Gen` |
| l4v `spec/design/skel`, `spec/machine` (Isabelle design and machine theories) | GPL-2.0-only | hand ports in `lean/Sel4Lean/Spec/` (MachineOps, Platform, PSpaceStorable, PSpaceInstances, KernelInit, Intermediate, DesignOnly); `Kernel_Config.thy` → generated `KernelConfig.lean` |
| l4v `spec/abstract`, `proof/refine` | GPL-2.0-only | the cancelSignal slice in `lean/Sel4Lean/Abstract`, `lean/Sel4Lean/Refine` |
| l4v `lib/` (Nondet_Monad, Nondet_VCG, Corres_UL, HaskellLib_H) | BSD-2-Clause | design of `lean/Sel4Lean/Monad`, `Corres.lean`, `Spec/HsPrelude.lean` |
| l4v `tools/haskell-translator` | BSD-2-Clause | conventions followed by `tools/hs2lean` (discriminators, skeleton directives) |
| [Isabelle](https://isabelle.in.tum.de) HOL theories | Isabelle license (BSD-style) | the Dedukti export spike in `artifacts/c5` |

seL4 and l4v: Copyright General Dynamics C4 Systems, Data61/CSIRO, Proofcraft Pty Ltd and contributors.
The l4v sources are not included in this repository; the build scripts fetch them.
