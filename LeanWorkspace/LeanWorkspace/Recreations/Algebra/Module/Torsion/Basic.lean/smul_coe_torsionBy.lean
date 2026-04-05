import Mathlib

variable {R M : Type*}

variable [CommSemiring R] [AddCommMonoid M] [Module R M] (s : Set R) (a : R)

theorem smul_coe_torsionBy (x : Submodule.torsionBy R M a) : a • (x : M) = 0 := x.prop

