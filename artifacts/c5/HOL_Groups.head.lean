import Isabelle.STTfa
import Isabelle.Pure
import Isabelle.session_Pure
import Isabelle.Tools_Code_Generator
import Isabelle.HOL_Groups_wp_orphans
import Isabelle.HOL_HOL
import Isabelle.HOL_Orderings
open STTfa
open Pure
open session_Pure
open Tools_Code_Generator
open HOL_Groups_wp_orphans
open HOL_HOL
open HOL_Orderings
set_option linter.unusedVariables false


namespace HOL_Groups

axiom zero_class_zero : ∀ _a__var : Set, El _a__var
axiom one_class_one : ∀ _a__var : Set, El _a__var
axiom plus_class_plus : ∀ {_a__var : Set}, El (arr _a__var (arr _a__var _a__var))
axiom minus_class_minus : ∀ {_a__var : Set}, El (arr _a__var (arr _a__var _a__var))
axiom uminus_class_uminus : ∀ {_a__var : Set}, El (arr _a__var _a__var)
axiom times_class_times : ∀ {_a__var : Set}, El (arr _a__var (arr _a__var _a__var))
axiom abs_class_abs : ∀ {_a__var : Set}, El (arr _a__var _a__var)
axiom sgn_class_sgn : ∀ {_a__var : Set}, El (arr _a__var _a__var)
@[reducible]
noncomputable def semigroup {_a__var : Set} : El (arr (arr _a__var (arr _a__var _a__var)) bool) := fun f__var : El (arr _a__var (arr _a__var _a__var)) => @All _a__var (fun a__var : El _a__var => @All _a__var (fun b__var : El _a__var => @All _a__var (fun c__var : El _a__var => @eq_const _a__var (f__var (f__var a__var b__var) c__var) (f__var a__var (f__var b__var c__var)))))
@[reducible]
noncomputable def abel_semigroup_axioms {_a__var : Set} : El (arr (arr _a__var (arr _a__var _a__var)) bool) := fun f__var : El (arr _a__var (arr _a__var _a__var)) => @All _a__var (fun a__var : El _a__var => @All _a__var (fun b__var : El _a__var => @eq_const _a__var (f__var a__var b__var) (f__var b__var a__var)))
@[reducible]
noncomputable def abel_semigroup {_a__var : Set} : El (arr (arr _a__var (arr _a__var _a__var)) bool) := fun f__var : El (arr _a__var (arr _a__var _a__var)) => conj (@semigroup _a__var f__var) (@abel_semigroup_axioms _a__var f__var)
@[reducible]
noncomputable def monoid_axioms {_a__var : Set} : El (arr (arr _a__var (arr _a__var _a__var)) (arr _a__var bool)) := fun f__var : El (arr _a__var (arr _a__var _a__var)) => fun z__var : El _a__var => conj (@All _a__var (fun a__var : El _a__var => @eq_const _a__var (f__var z__var a__var) a__var)) (@All _a__var (fun a__var : El _a__var => @eq_const _a__var (f__var a__var z__var) a__var))
@[reducible]
noncomputable def monoid {_a__var : Set} : El (arr (arr _a__var (arr _a__var _a__var)) (arr _a__var bool)) := fun f__var : El (arr _a__var (arr _a__var _a__var)) => fun z__var : El _a__var => conj (@semigroup _a__var f__var) (@monoid_axioms _a__var f__var z__var)
@[reducible]
noncomputable def comm_monoid_axioms {_a__var : Set} : El (arr (arr _a__var (arr _a__var _a__var)) (arr _a__var bool)) := fun f__var : El (arr _a__var (arr _a__var _a__var)) => fun z__var : El _a__var => @All _a__var (fun a__var : El _a__var => @eq_const _a__var (f__var a__var z__var) a__var)
@[reducible]
noncomputable def comm_monoid {_a__var : Set} : El (arr (arr _a__var (arr _a__va