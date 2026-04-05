import Mathlib

variable {M : Type*}

theorem quotient_mk_eq_mk [Monoid M] (a : M) : ⟦a⟧ = Associates.mk a := Associated.rfl

