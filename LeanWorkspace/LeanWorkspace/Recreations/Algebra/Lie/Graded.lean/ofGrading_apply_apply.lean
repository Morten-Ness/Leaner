import Mathlib

variable {ι σ R L : Type*}

variable [DecidableEq ι] [AddCommMonoid ι] [CommRing R] [LieRing L] [LieAlgebra R L]
  (ℒ : ι → Submodule R L) [GradedLieAlgebra ℒ]

theorem ofGrading_apply_apply (φ : ι →+ R) {i : ι} {a : L} (ha : a ∈ ℒ i) :
    LieDerivation.ofGrading ℒ φ a = φ i • a := by
  simp [LieDerivation.ofGrading, decomposeLinearEquiv_apply, decompose_of_mem ℒ ha]
  simp [decomposeLinearEquiv_symm_apply]

