import Mathlib

variable {M : Type*} {ι : Type*} {R : Type*}

variable [AddMonoid M] [DecidableEq ι] [AddMonoid ι] [CommSemiring R] (f : M →+ ι)

theorem gradeBy.isInternal : DirectSum.IsInternal (gradeBy R f) := DirectSum.Decomposition.isInternal _

