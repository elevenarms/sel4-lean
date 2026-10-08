import Sel4Lean.Spec.Prelude

/-!
# Kernel configuration (hand-written, W3): l4v's `spec/machine/RISCV64/Kernel_Config.thy`

The Haskell model leaves the build configuration to Isabelle (`Config.lhs`: `timeSlice = error "see
Kernel_Config.thy"`, …), and l4v's design skeletons exclude a few Haskell definitions in favour of
Isabelle ones (`design/skel/Config_H.thy`: `NOT numDomains timeSlice resetChunkBits retypeFanOutLimit`;
`design/skel/RISCV64/Hardware_H.thy`: `NOT physBase …`, defined in `machine/RISCV64/Platform.thy` from this
file). hs2lean aliases those names to the definitions here (`full.py`: `L4V_OVERRIDES`).

Values are those of l4v's checked-in RISCV64 (HiFive) configuration. One differs from the Haskell model:
`physBase` is `0x80200000` here (the kernel's load address, as in C) and `0x80000000` in
`Hardware/RISCV64/HiFive.hs`; the verified spec uses this one.
-/

namespace Sel4Lean.Spec.KernelConfig
open Sel4Lean.Exec (Word)

/-- `physBase ≡ 0x80200000` -/
def physBase : PAddr := PAddr.PAddr 0x80200000
/-- `maxIRQ ≡ 54` (from platform_gen.h) -/
def maxIRQ : Nat := 54
/-- `irqBits ≡ 6` -/
def irqBits : Nat := 6
/-- `timeSlice ≡ 5` (CONFIG_TIME_SLICE) -/
def timeSlice : Nat := 5
/-- `retypeFanOutLimit ≡ 256` (CONFIG_RETYPE_FAN_OUT_LIMIT) -/
def retypeFanOutLimit : Word := 256
/-- `workUnitsLimit ≡ 100` (CONFIG_MAX_NUM_WORK_UNITS_PER_PREEMPTION) -/
def workUnitsLimit : Nat := 100
/-- `resetChunkBits ≡ 8` (CONFIG_RESET_CHUNK_BITS) -/
def resetChunkBits : Nat := 8
/-- `numDomains ≡ 16` (CONFIG_NUM_DOMAINS) -/
def numDomains : Nat := 16
/-- `numPriorities ≡ 256` (CONFIG_NUM_PRIORITIES) -/
def numPriorities : Nat := 256
/-- `CONFIG_ROOT_CNODE_SIZE_BITS ≡ 19` -/
def rootCNodeSizeBits : Nat := 19

end Sel4Lean.Spec.KernelConfig
