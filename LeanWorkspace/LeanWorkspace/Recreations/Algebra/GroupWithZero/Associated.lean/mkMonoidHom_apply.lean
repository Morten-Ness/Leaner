import Mathlib

variable {M : Type*}

variable [CommMonoid M]

theorem mkMonoidHom_apply (a : M) : Associates.mkMonoidHom a = Associates.mk a := Associated.rfl

