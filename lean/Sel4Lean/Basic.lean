/-!
# Toolchain smoke test (C1)

Checks the pinned toolchain has what crawl relies on: `BitVec` for machine words
(Isabelle's `'a word` becomes `BitVec n`), `decide`, `omega` and `simp`.
Replaced by real modules from C2 on.
-/

namespace Sel4Lean

/-- RISCV64 machine word, as in l4v's `machine_word = 64 word`. -/
abbrev MachineWord := BitVec 64

/-- Pointer alignment test of the kind l4v uses everywhere (`is_aligned p n`). -/
def isAligned (p : MachineWord) (n : Nat) : Bool :=
  p &&& (BitVec.ofNat 64 (2 ^ n - 1)) == 0

example : isAligned 0x1000#64 12 = true := by decide
example : isAligned 0x1008#64 12 = false := by decide

theorem word_add_comm (a b : MachineWord) : a + b = b + a := BitVec.add_comm a b

example (n : Nat) (h : n < 64) : n + 1 ≤ 64 := by omega

end Sel4Lean
