import Mathlib

variable {M : Type*}

variable [CommMonoid M]

theorem mk_mul_mk {x y : M} : Associates.mk x * Associates.mk y = Associates.mk (x * y) := Associated.rfl

