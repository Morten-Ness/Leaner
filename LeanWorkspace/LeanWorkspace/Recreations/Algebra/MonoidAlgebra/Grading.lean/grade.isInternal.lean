import Mathlib

variable {M : Type*} {ι : Type*} {R : Type*}

variable [AddMonoid M] [DecidableEq ι] [AddMonoid ι] [CommSemiring R] (f : M →+ ι)

theorem grade.isInternal : DirectSum.IsInternal (grade R : ι → Submodule R _) := DirectSum.Decomposition.isInternal _

