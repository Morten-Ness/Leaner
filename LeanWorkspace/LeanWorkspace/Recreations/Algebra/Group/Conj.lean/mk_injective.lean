import Mathlib

variable {α : Type u} {β : Type v}

variable [CommMonoid α]

theorem mk_injective : Function.Injective (@ConjClasses.mk α _) := fun _ _ =>
  (ConjClasses.mk_eq_mk_iff_isConj.trans isConj_iff_eq).1

