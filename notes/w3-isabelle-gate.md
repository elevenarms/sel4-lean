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

## Structured values and specification strength

Two further checks, both against the same `ExecSpec` heap:

- **Structured values** (`env/remote/w3_isagate2.sh`, `tools/hs2lean/isagate2.py`,
  `env/remote/isagate/Eval2.ML`).
  - Coverage: 80 pure spec functions over capabilities, kernel objects, enumerations, options and pairs
    (`sameRegionAs`, `maskCapRights`, `updateCapData`, `isCapRevocable`, `objBitsKO`, …).
  - Inputs: generated from the Lean constructors (parsed from `Gen/Types.lean`) and rendered twice, as a
    Lean term and as a typed Isabelle term with full constant names. A Haskell newtype is a type synonym in
    Isabelle unless l4v keeps its constructor, and the constant table says which.
  - Isabelle evaluation: by code evaluation, else by rounds of unfolding l4v's own definitions followed by
    simplification. Constructors and case combinators are never unfolded. The datatypes' case equations
    are added, because types declared in `context Arch` keep their simp rules local.
  - Isolation: the cases run in chunks of 10, each in its own `isabelle process_theories` (6 in parallel),
    so one pathological case costs only its chunk.
  - Comparison: as S-expressions.
  - Result: **74/79 functions agree on every case; 474 cases: 429 agree, 26 undefined in both, 0 differ.**
    The 19 cases Isabelle does not evaluate are its limits, not Lean's: large `nat` powers in
    `maxFreeIndex`/`getFreeRef`, `toEnum` on invocation labels, and an out-of-range list index in
    `parseTimeArg` (Haskell `error`).
- **Specification strength** (`isagate.py names`). A constant l4v *declares but never defines* (`consts`,
  or `decls_only` without a body) is unspecified in Isabelle; Lean must not define it either, or Lean
  proves facts Isabelle cannot.
  - What it found: 17 Haskell bodies the verified spec deliberately leaves out. Most are the state
    assertions behind `stateAssert` (`deletionIsSafe`, `ksASIDMapSafe`, `pointerInUserData`,
    `capHasProperty`, `ready_qs_runnable`, …); also `cNodeOverlap`, `archOverlap`,
    `canonicalAddressAssert` and `checkPTAt`.
  - Fix: the gate writes the list (`unspecified-names.txt`) and the translator emits those names as
    opaque stubs. **51/51** unspecified in both.

The structured gate also showed that Isabelle's `irq` is **6 bits** (`irq_len = Kernel_Config.irqBits`),
where the Haskell has `Word32`. `RISCV64.IRQ` is now 6 bits wide.

Recursive functions are now total `def`s wherever Lean proves termination itself. Only `cteDelete`,
`cteRevoke`, `finaliseSlot`, `reduceZombie` and `resolveAddressBits` stay `partial`, plus the page-table
lookups in `Kernel_VSpace_RISCV64`. These are the ones l4v also needs hand termination arguments for.

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
