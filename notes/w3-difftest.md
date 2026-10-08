# W3: differential test against the Haskell model

**Result (2026-10-08):** 60 of 60 testable functions agree with l4v's Haskell model on all 158 cases.
Getting there found five translator bugs, every one of which compiled cleanly.

## What runs

`env/remote/w3_difftest.sh` on the instance, driven by `tools/hs2lean/difftest.py`:

1. **Pick functions.** `difftest.py gen` takes every top-level function or constant in a module that
   compiles (`artifacts/w2/compile-status.txt`) and keeps it if it qualifies:
   - it is exported, so GHCi can call it as `Module.f`;
   - its signature is monomorphic over word-like types: `Word`, `Word8`–`Word64`, `Domain`, `Priority`,
     `Int`, `Bool`, the `CPtr`/`VPtr`/`PAddr`/`ASID` newtypes, or `PPtr a`, where a polymorphic pointee is
     instantiated at the unit type on both sides.

   Boot modules are skipped.
2. **Make inputs.** Each function gets 8 inputs from a fixed seed (20261008). Boundary values come
   first (0, 1, 2, 7, 4095, 4096, the top value, the top bit), limited to what fits the type's width.
   The rest are random.
3. **Haskell side.** `Test.ghci` runs in `cabal v2-repl` on l4v's own RISCV64 build, inside the
   `trustworthysystems/l4v` image. It prints `id|value` lines.
4. **Lean side.** `DiffTest.lean` has one `#eval` per case, run with `lake env lean` against the
   generated modules.
5. **Compare.** `difftest.py compare` matches the two outputs by case id and writes
   `artifacts/w3/difftest.tsv`.

## Verdicts

| verdict | cases | meaning |
|---|---:|---|
| agree | 146 | same value |
| int-nat | 4 | Haskell `Int` went negative, while Lean's `Nat` truncates to 0 (`invertL1Index` for i ≥ 4, outside its domain) |
| hs-error | 8 | Haskell calls `error`, e.g. `Config` values that live in `Kernel_Config.thy`. The translation's `default` refines `undefined`, as in l4v |
| DIFFER | 0 | |
| lean-missing / hs-missing | 0 | |

`int-nat` is the one deliberate semantic gap. l4v's haskell-translator makes the same mapping, `Int` to
`nat`. It matters only if a caller passes `i ≥ l2BitmapSize`. Expected callers pass L1 bitmap indices
below that bound, but this is unverified; it is a W4 obligation (a guard lemma at the call sites).

## What it caught

The first run had 24 DIFFER cases and 88 missing ones. Every DIFFER came from the translator.
None came from the Haskell model.

| bug | symptom | fix (`full.py`) |
|---|---|---|
| Every function in `Machine/Hardware*` was stubbed as machine interface | `pageBits`, `pptrBase`, `ptBitsLeft`, … evaluated to `default` (0) | Only signatures mentioning `MachineMonad`/`IO`/`Ptr`/`MachineData` are opaque. Machine-opaque functions went from 99 to 59. |
| The `PLATFORM` import placeholder was never resolved | `fromPAddr = fromPAddr`, which loops; `physBase` unknown | `PLATFORM` maps to the platform module, and `Platform.f` goes through import, record-selector alias or stub |
| Wrong platform | The test above showed GHC calling `RISCV64/HiFive.hs` | l4v builds **HiFive** (`SEL4.cabal`, `make_spec.sh`), not Spike: `maxIRQ` is 54, not 53. Other platforms are now excluded like other architectures |
| Import lists ignored | `import …PLATFORM (irqInvalid)` brought all of HiFive's types into scope, so the generic `IRQ` became `RISCV64.IRQ` | `unqualified_imports` keeps import lists, and `visible_from` checks them |
| The `"Ptr "` substring matched `PPtr a` | `ptrFromPAddr` was stubbed as a machine op | Whole-word regex |

The harness had its own problems:
- `Word` was ambiguous in GHCi; fixed with `import Prelude hiding (Word)`.
- Newtype selectors were ambiguous; fixed by unwrapping with constructor patterns.
- `Word8` literal overflow; fixed by limiting inputs to the type's width.
- Non-exported names were tested; they are now filtered by the export list.
- Polymorphic `PPtr a` left metavariables on the Lean side; fixed with a unit pointee.

## Limits

- Only pure functions over words. Anything in `Kernel`, any function taking `KernelState` or object
  records, and any polymorphic function is out of scope here. Testing monadic functions needs a
  state generator and the machine-state model, which is the next W3 item.
- Agreement on sampled inputs is evidence, not proof. The proofs in W4 are what count; this test
  checks that the thing W4 will prove things about is the thing l4v specifies.
