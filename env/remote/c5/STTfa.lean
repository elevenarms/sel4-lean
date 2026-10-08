/-!
# Simple type theory encoding, made concrete (C5 spike, hand-written)

Lambdapi's `STTfa.lp` declares these symbols and adds **rewrite rules**:
```
rule El (arr $a $b) ↪ El $a → El $b
rule Prf (imp $a $b) ↪ Prf $a → Prf $b
with Prf (@all $a $b) ↪ Π x: El $a, Prf ($b x)
```
The Lean exporter drops rewrite rules and emits plain axioms, so terms like
`fun x : El bool => x : El (arr bool bool)` would not type-check. Defining the symbols turns each rule
into a definitional equality instead.
-/

namespace STTfa

def Set : Type 1 := Type
def arr (a b : Set) : Set := a → b
def El (a : Set) : Type := a
def prop : Set := Prop
def imp (a b : El prop) : El prop := a → b
def all {a : Set} (f : El a → El prop) : El prop := ∀ x, f x
def Prf (p : El prop) : Prop := p

end STTfa
