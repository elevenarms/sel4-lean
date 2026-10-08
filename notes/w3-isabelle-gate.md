# W3: the Lean spec against l4v's Isabelle (the interchangeability gate)

**Result (2026-10-08):**
- All 62 generated modules compile, boot code included.
- Every one of the 1319 constants in l4v's built executable spec (Isabelle session `ExecSpec`) has a Lean
  declaration of the same name.
- All 60 testable functions agree with Isabelle's own evaluation of that spec on every case (155 equal
  values, 3 where both sides are `undefined`).

## Why Isabelle, not just GHC

The proofs l4v checks are about its Isabelle design spec (`spec/design/*.thy`), not about the Haskell model.
l4v builds that spec from the Haskell with its own translator, driven by *skeleton* theories
(`spec/design/skel`, `spec/design/m-skel`). Each skeleton line `#INCLUDE_HASKELL file … NOT a b c` pulls in
a Haskell module minus a list of definitions, and the skeleton supplies hand-written Isabelle in their
place. A Lean spec that should be interchangeable with l4v's has to follow the same construction. The
Haskell model (GHC) is evidence; l4v's Isabelle is the reference.

`tools/hs2lean/skel.py dropped` reads all the directives. It finds 105 definitions that l4v drops from the
Haskell modules it includes, and 15 Haskell modules it does not include at all.

## The gate

`env/remote/w3_isagate.sh` runs a session `LeanGate` on top of l4v's built `ExecSpec` heap, inside l4v's
own container image. There are two checks:

- **Names** (`Consts.thy`, `isagate.py names`): every constant ExecSpec defines (3834). Isabelle internals
  are filtered out: record and datatype machinery, the function package, Quickcheck, class predicates.
  That leaves 1319 constants, each matched to a Lean declaration by name: **1319/1319**.
- **Values** (`Values.thy`, `isagate.py gen/compare`): the difftest's cases, mapped to their ExecSpec
  constants. Each case is built as a typed term in ML (no parsing) and evaluated by Isabelle. If code
  generation fails, the term is first unfolded with the definitional axioms of the ExecSpec constants it
  uses, then simplified with Isabelle's own simp set. Result: **60/60 functions**.

The GHC difftest is now *adjudicated* by Isabelle: a Lean/Haskell difference is accepted (verdict `l4v`)
only when Lean equals Isabelle.

## What the gate found

Each of these compiled, and some passed the GHC test:

| finding | Haskell model | l4v (verified) | Lean now |
|---|---|---|---|
| `pptrUserTop` | `pptrBase` | `mask canonical_bit && ~~mask 12` = `0x3FFFFFF000` (Platform.thy) | l4v's |
| `physBase` | `0x80000000` (HiFive.hs) | `0x80200000` (Kernel_Config.thy, as in C) | l4v's |
| CTE `loadObject`/`updateObject` | **overridden** to reach the 5 CTE slots inside a TCB | `loadObject_cte`/`updateObject_cte` | ported; the earlier Lean gave CTEs the default methods, which is wrong for TCB slots |
| `foldME` (untyped split at boot) | `foldM`, left to right (bits 4→62) | `foldr …`, **right to left** (62→4) | l4v's order |
| `error` | bottom | `error ≡ λx. undefined` (HaskellLib_H) | opaque `undefinedH` (was `default`, which let Lean prove more than Isabelle can) |
| partial field selectors | bottom on other constructors | `primrec`, unspecified there | `undefinedH` (was `default`) |
| `invertL1Index` for i ≥ 4 | negative `Int` | `nat` subtraction, truncates to 0 | same as Isabelle (what the GHC test called "int-nat") |

## What was ported from l4v's hand-written Isabelle

| Lean file | l4v source | contents |
|---|---|---|
| `Spec/Gen/KernelConfig.lean` | `machine/RISCV64/Kernel_Config.thy` | **generated** by `kconfig.py`: 47 configuration values |
| `Spec/Platform.lean` | `machine/RISCV64/Platform.thy` | memory layout, `ptrFromPAddr`, `irqInvalid`, … |
| `Spec/MachineOps.lean` | `machine/RISCV64/MachineOps.thy`, `MachineMonad.thy` | machine operations, IRQ oracle (no axiom), user monad |
| `Spec/PSpaceStorable.lean`, `PSpaceInstances.lean` | `PSpaceStorable_H.thy`, `ObjectInstances_H.thy` | `pre_storable`/`pspace_storable` with their laws as fields, proved for all 8 instances; `kernel_object_type`, `koTypeOf` |
| `Spec/KernelInit.lean` | `KernelInitMonad_H.thy`, `KernelInit_H.thy` | the init monad (kernel state inside `init_data`), `doKernelOp`, `runInit`, unspecified bootinfo constants, `newKernelState` |
| `Spec/Intermediate.lean` | `Intermediate_H.thy`, `RISCV64/ArchIntermediate_H.thy` | the "old Haskell" object and capability creation used by the Retype proofs |
| `Spec/DesignOnly.lean` | `Delete_H`, `FaultMonad_H`, `State_H`, `PSpaceStruct_H`, `API_H` | `slotsPointed`, `finaliseSlot'`, `nothingOnFailure`, unspecified kernel assertions, … |
| translator (`full.py`) | `lhs_pars.py` conventions | `isC` discriminators (88); l4v's `kernel_state` (`ksMachineState`, `gsMaxObjectSize`), `init_data`, `user_context`; `L4V_OVERRIDES` aliases the 105 dropped names |

## Boot code

`Kernel/Init.lhs` now runs in l4v's init monad. `Kernel/BootInfo.lhs` is not in l4v's spec, but it compiles
too. Three translator gaps showed up on the way:
- Haskell's let-polymorphism (`let p = ptrFromPAddr x`, used at several pointer types);
- unconstrained pointee types (`reserveFrame :: PPtr a -> …`);
- positional `do` scoping (a later `value <- …` does not shadow an earlier use of the selector `value`).

## Limits

- **Values** cover only pure functions over words, booleans and word newtypes. Datatype arguments
  (capabilities, objects) and monadic functions over generated states are the next extension of the gate.
- **Names** are matched by base name. Types are not yet compared constant by constant.
- **`partial` defs** (18, from W2) still hide their bodies; l4v proves termination (`finaliseSlot'`,
  `cteDeleteOne'`). W4.
