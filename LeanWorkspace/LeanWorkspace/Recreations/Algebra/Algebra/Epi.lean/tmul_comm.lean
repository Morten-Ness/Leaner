import Mathlib

variable (R A : Type*) [CommSemiring R] [CommSemiring A] [Algebra R A] [Algebra.IsEpi R A]

theorem tmul_comm (a b : A) :
    a ⊗ₜ[R] b = b ⊗ₜ[R] a := by
  have (a b : A) := calc a ⊗ₜ[R] b
      = a • (1 ⊗ₜ[R] b) := by rw [tmul_eq_smul_one_tmul]
    _ = a • (b ⊗ₜ[R] 1) := by rw [(Algebra.isEpi_iff_forall_one_tmul_eq R A).mp inferInstance b]
    _ = a • (b • (1 ⊗ₜ[R] 1)) := by rw [tmul_eq_smul_one_tmul]
  rw [this a b, this b a, smul_comm]

