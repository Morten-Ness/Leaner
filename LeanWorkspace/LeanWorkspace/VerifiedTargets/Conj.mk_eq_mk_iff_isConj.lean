import Mathlib

variable {α : Type u} {β : Type v}

variable [Monoid α] [Monoid β]

theorem mk_eq_mk_iff_isConj {a b : α} : ConjClasses.mk a = ConjClasses.mk b ↔ IsConj a b := Iff.intro Quotient.exact Quot.sound

