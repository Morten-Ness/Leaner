import Mathlib

variable {R M : Type*}

variable [CommSemiring R] [AddCommMonoid M] [Module R M] (s : Set R) (a : R)

theorem smul_torsionBy (x : Submodule.torsionBy R M a) : a • x = 0 := Subtype.ext x.prop

