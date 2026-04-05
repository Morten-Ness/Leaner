import Mathlib

variable {M : Type*}

theorem one_eq_mk_one [Monoid M] : (1 : Associates M) = Associates.mk 1 := Associated.rfl

