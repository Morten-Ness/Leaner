import Mathlib

variable {S T R : Type*} [CommRing R] (r x y : R) (a b : ℍ[R])

theorem normSq_smul (r : R) (q : ℍ[R]) : Quaternion.normSq (r • q) = r ^ 2 * Quaternion.normSq q := by
  simp only [Quaternion.normSq_def', Quaternion.re_smul, imI_smul, imJ_smul, imK_smul, mul_pow, mul_add, smul_eq_mul]

