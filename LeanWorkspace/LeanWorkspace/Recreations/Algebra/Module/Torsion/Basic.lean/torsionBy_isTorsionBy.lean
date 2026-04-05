import Mathlib

variable {R M : Type*}

variable [CommSemiring R] [AddCommMonoid M] [Module R M] (s : Set R) (a : R)

theorem torsionBy_isTorsionBy : IsTorsionBy R (Submodule.torsionBy R M a) a := Submodule.smul_torsionBy a

