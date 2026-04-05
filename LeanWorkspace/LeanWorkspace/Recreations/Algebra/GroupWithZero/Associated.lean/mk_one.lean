import Mathlib

variable {M : Type*}

theorem mk_one [Monoid M] : Associates.mk (1 : M) = 1 := Associated.rfl

