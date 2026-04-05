import Mathlib

variable {ι σ R L : Type*}

variable [DecidableEq ι] [AddCommMonoid ι] [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : ι → Submodule R L) [GradedLieAlgebra ℒ]

theorem ofGradingSum_of (φ : ι →+ R) (i : ι) (a : ℒ i) :
    LieDerivation.ofGradingSum ℒ φ (of (ℒ ·) i a) = (φ i) • (of (ℒ ·) i a) := by
  simp [← lof_eq_of R, LieDerivation.ofGradingSum]

