import Sel4Lean.Spec.Prelude
import Sel4Lean.Spec.Gen.KernelConfig

/-!
# Platform constants (hand-written, W3): l4v's `spec/machine/RISCV64/Platform.thy`

l4v's design skeleton drops these definitions of `Machine/Hardware/RISCV64.hs` (`Hardware_H.thy`:
`#INCLUDE_HASKELL … NOT … pptrUserTop …`) and defines them in `Platform.thy`, which states the C kernel's
memory layout. They keep the Haskell signatures here (`VPtr`, `PAddr`, `PPtr a`; Isabelle has
`machine_word` throughout) so the generated code can use them unchanged.

Where the values differ from the Haskell model the verified spec wins: `pptrUserTop` is
`mask canonical_bit && ~~mask 12 = 0x3FFFFFF000` (Haskell: `pptrBase`), and `physBase` is
`Kernel_Config.physBase` (see `KernelConfig.lean`). Found by the Isabelle value gate (`tools/hs2lean/isagate.py`).
-/

namespace Sel4Lean.Spec.Platform
open Sel4Lean.Exec (Word PPtr)

/-- `canonical_bit = 38` -/
def canonical_bit : Nat := 38
/-- `kdevBase = - (1 << 30)` -/
def kdevBase : Word := -((1 : Word) <<< 30)
/-- `physBase` (Kernel_Config.thy; Haskell's HiFive module says 0x80000000), at the Haskell type -/
def physBase : PAddr := PAddr.PAddr KernelConfig.physBase
/-- `kernelELFPAddrBase = physBase` -/
def kernelELFPAddrBase : PAddr := physBase
/-- `pptrTop ≡ - (1 << 31)` -/
def pptrTop : VPtr := VPtr.VPtr (-((1 : Word) <<< 31))
/-- `kernelELFBase = pptrTop + (kernelELFPAddrBase && mask 30)` -/
def kernelELFBase : VPtr := VPtr.VPtr (pptrTop.fromVPtr + (kernelELFPAddrBase.fromPAddr &&& (((1 : Word) <<< 30) - 1)))
/-- `kernelELFBaseOffset = kernelELFBase - kernelELFPAddrBase` -/
def kernelELFBaseOffset : Word := kernelELFBase.fromVPtr - kernelELFPAddrBase.fromPAddr
/-- `pptrBase = - (1 << canonical_bit)` -/
def pptrBase : VPtr := VPtr.VPtr (-((1 : Word) <<< canonical_bit))
/-- `pptrUserTop ≡ mask canonical_bit && ~~mask 12` (page-aligned; the Haskell model says `pptrBase`) -/
def pptrUserTop : VPtr := VPtr.VPtr ((((1 : Word) <<< canonical_bit) - 1) &&& ~~~(((1 : Word) <<< 12) - 1))
/-- `paddrBase ≡ 0` -/
def paddrBase : PAddr := PAddr.PAddr 0
/-- `pptrBaseOffset = pptrBase - paddrBase` -/
def pptrBaseOffset : Word := pptrBase.fromVPtr - paddrBase.fromPAddr
/-- `ptrFromPAddr paddr ≡ paddr + pptrBaseOffset` -/
def ptrFromPAddr {a : Type} (p : PAddr) : PPtr a := ⟨p.fromPAddr + pptrBaseOffset⟩
/-- `addrFromPPtr pptr ≡ pptr - pptrBaseOffset` -/
def addrFromPPtr {a : Type} (p : PPtr a) : PAddr := PAddr.PAddr (p.ptr - pptrBaseOffset)
/-- `addrFromKPPtr pptr ≡ pptr - kernelELFBaseOffset` -/
def addrFromKPPtr {a : Type} (p : PPtr a) : PAddr := PAddr.PAddr (p.ptr - kernelELFBaseOffset)
/-- `toPAddr ≡ id` (abbreviation) -/
def toPAddr (w : Word) : PAddr := PAddr.PAddr w
/-- `irqInvalid ≡ 0` -/
def irqInvalid : RISCV64.IRQ := ⟨0⟩
/-- `pageColourBits ≡ undefined` (not implemented on this platform) -/
noncomputable def pageColourBits : Nat := undefinedH

end Sel4Lean.Spec.Platform
