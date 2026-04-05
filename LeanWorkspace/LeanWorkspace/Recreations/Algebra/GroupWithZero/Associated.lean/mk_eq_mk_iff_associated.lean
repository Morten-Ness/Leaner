import Mathlib

variable {M : Type*}

theorem mk_eq_mk_iff_associated [Monoid M] {a b : M} : Associates.mk a = Associates.mk b ↔ a ~ᵤ b := Iff.intro Quotient.exact Quot.sound

