import Mathlib

variable (R S M A : Type*)

variable [AddCommMonoid M]

variable [CommSemiring R] [Semiring S] [Algebra R S] [Module S M]

theorem RestrictScalars.addEquiv_symm_map_smul_smul (r : R) (s : S) (x : M) :
    (RestrictScalars.addEquiv R S M).symm ((r • s) • x) =
      r • (RestrictScalars.addEquiv R S M).symm (s • x) := by
  rw [Algebra.smul_def, mul_smul]
  rfl

