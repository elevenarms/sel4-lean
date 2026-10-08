# W2: Translating the whole Haskell spec

Status: **in progress** (2026-10-08).

## Numbers (RISCV64, l4v ac4a36d)

| Metric | Value | Source |
|---|---|---|
| Data types translated (closure of all modules) | **91+**, 1 opaque (`CallbackData` has no constructors in Haskell either) | `Spec/Gen/Types.lean`, compiles |
| Functions translated to Lean text | **679 / 695 (97.7%)** (incl. `Data/` helper modules) | `artifacts/w2/coverage.tsv` |
| Machine-interface functions | **99**, opaque **by design**: the Haskell bodies are the simulator's (IO/FFI); l4v's Isabelle also treats machine operations as opaque (`MachineOps.thy`) | `full.py` `MACHINE_INTERFACE` |
| Modules whose generated Lean compiles | **48 / 61** | `artifacts/w2/compile-status.txt` |
| Translated bodies in compiling modules | **300 / 596 non-machine functions (50.3%)**; 8 of them `partial` | the honest number |
| `partial def` (self-recursive) | 16 in all generated modules; each checked to be genuinely recursive | TODO(W4): termination proofs |

Translation coverage is not compile coverage. A module compiles only when every function in it does, so
the large modules (`Kernel/Init`, `Kernel/VSpace/RISCV64`, `Model/PSpace`, `Object/CNode`, `Object/TCB`,
`Object/Interrupt`) still fail on a few errors each.

## How it works

- `tools/hs2lean/full.py types`: index every RISCV64-relevant declaration in the spec; translate the type
  closure; pointer cycles become `mutual` blocks (Tarjan SCCs); generic/arch name clashes resolve per file
  (`Arch.X`, re-exports like `type PAddr = Arch.PAddr`).
- `tools/hs2lean/full.py module`: translate one module into its own namespace; every name it uses from
  elsewhere gets an `opaque` stub **generated from its Haskell signature** (`Arch.f` → RISCV64 signature).
  The hand-written crawl stubs are reproduced exactly by this.
- `env/remote/w2_compile_sweep.sh`: regenerate everything, build all modules, write status.
- `lean/Sel4Lean/Spec/HsPrelude.lean`: Haskell base library over `NondetM` (hand-written).

## Modelling decisions (following l4v's Isabelle model where it exists)

| Haskell | Lean | Note |
|---|---|---|
| `Kernel` | `NondetM KernelState` | l4v `kernel = (kernel_state, 'a) nondet_monad` |
| `State s` (e.g. `UserMonad`) | `NondetM s` | |
| `ExceptT e m` | Lean `ExceptT` = `m (Except e α)` | l4v `(e + 'a) s_monad` |
| `StateT`, `ReaderT`, `IO` | Lean core | machine/boot plumbing, outside the refinement proofs |
| `Data.Map.Map k v` | `k → Option v` | l4v models `psMap` the same way |
| `Array i e` | `i → e`; `//` = `arrayUpdH` | |
| `Data.Set.Set a` | `a → Prop` | Isabelle sets |
| `Int` | `Nat` | as l4v's translator |
| `Word` (spec newtype over `Word64`) | `BitVec 64` | l4v `machine_word = 64 word` |
| `error`, `undefined`, `head []` | `default` (= `fail` in the kernel monad) | l4v `haskell_fail` / `undefined` |
| partial selectors, omitted record fields | `default` | Isabelle's underspecified selectors |
| self-recursive functions | `partial def` **(temporary)** | hides the body from proofs; W4 needs termination proofs like l4v's |

## A silent mistranslation, found and fixed

Guarded definitions (`f x | c1 = e1 | otherwise = e2`) parse as several `match` nodes. Until 2026-10-08 the
translator read only the first one **and ignored its guard**, so every guarded function, local function and
`case` alternative in the spec was translated as if its first branch always applied. It compiled, so nothing
flagged it; it surfaced as `nullProtect := fun f m => none` in `Model/PSpace`. Now every right-hand side goes
through one guard-aware path (`rhs()` in `hs2lean.py`): if-chains, `otherwise` as the final else, `default`
when the last equation's guards all fail, and a refusal (not an approximation) when guards would fall through
to a later equation. `test_hs2lean.py` has regression tests. Lesson: "compiles" is not "correct", and the
side-by-side tests (W3) matter.

## Machine interface (as l4v)

`MachineMonad` is `ReaderT MachineData IO` in Haskell (the simulator). Following l4v's Isabelle
(`machine_monad = (machine_state, 'a) nondet_monad`), it is `NondetM MachineState` here, with `MachineState`
opaque for now, and machine operations are opaque stubs from their signatures. `doMachineOp` is a
placeholder: l4v lifts machine operations through `ksMachineState`, a field the Haskell `KernelState`
lacks (TODO(W3): model the machine state).

## Second near-miss: `partial` everywhere

The recursion check (which marks functions `partial`, hiding their bodies from proofs) first counted a
function's own name in its defining equation, then the `f` inside a dispatch `f = Arch.f`. For a while 76
functions were `partial`, 58 of them not recursive at all. It compiled either way, so only an explicit audit
caught it. The check now looks only at unqualified names in right-hand sides and `where` clauses; all 16
remaining `partial` defs are self-recursive.

## Hand-written layer

- `Spec/HsPrelude.lean`: Haskell base library, `MonadFailH` (Haskell `MonadFail`), `OrdH` (`Ord`),
  `MapH` (`Data.Map` over `k → Option v`; `null`/`findMin`/`findMax` noncomputable via choice; `keys` still
  unspecified, TODO).
- `Spec/PSpaceStorable.lean`: the spec's only user-defined class and its 8 instances, shaped like l4v's
  Isabelle `pspace_storable` (`projectKO_opt`). `objBitsKO`, `nullMDBNode`, TCB/ASIDPool `makeObject` are
  still opaque here (TODO: use generated definitions once modules import each other).

## Fixes along the way (each a class of errors)

Haskell `deriving` clauses mistaken for type references; qualified library names (`Data.Word.Word64`);
re-exported synonyms and `newtype X = X Arch.X` wrappers; generic vs RISCV64 names (`Register`, `IRQ`)
inside arch modules, for types *and* constructors; constructor names equal to type names; multi-name record
fields; newtype `deriving (Num, Ord, Bits, Enum)` → lifted instances; enumerations → explicit index maps;
multi-equation functions and pattern parameters → `match`; backtick operators and fixities; sections;
destructuring `where` bindings; `Arch.f` dispatch (`f = Arch.f` would otherwise be an infinite self-call).

Two process lessons: generated files are tracked in git, so a laptop `remote_push.sh` can overwrite fresh
output with stale copies; the sweep therefore regenerates first. And Lake prints `⚠ Built` for modules that
compile with warnings; the sweep first counted only `✔`.

## Next

The remaining failures are concentrated: type mismatches around monad stacks (`KernelF`, `KernelInit`,
`MachineMonad` vs `Kernel`), typeclass methods with no top-level signature (`makeObject`, `loadObject` from
`PSpaceStorable`), `show`, `liftIO`, `maxBound`/`minBound`, and numeric literal typing. Target the large
modules one at a time, since they hold most of the functions.
