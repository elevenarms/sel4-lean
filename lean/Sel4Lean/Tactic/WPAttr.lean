import Lean

/-!
# `@[wp_rule]`: the rule set for the `wp` tactic (l4v's `[wp]` attribute)

Kept in its own module because an environment extension can't be used in the file that declares it.
-/

namespace Sel4Lean
open Lean

/-- Declarations tagged `@[wp_rule]`, in tagging order. -/
initialize wpRuleExt : SimpleScopedEnvExtension Name (Array Name) ←
  registerSimpleScopedEnvExtension { addEntry := fun s n => s.push n, initial := #[] }

initialize registerBuiltinAttribute {
  name := `wp_rule
  descr := "weakest-precondition rule used by the `wp` tactic (l4v `[wp]`)"
  add := fun decl _stx kind => wpRuleExt.add decl kind
}

end Sel4Lean
