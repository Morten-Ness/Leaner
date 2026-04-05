import Mathlib

open scoped Ring Kronecker

variable {l : Type*} {m : Type u} {n : Type u'} {α : Type v}

variable [Fintype n] [DecidableEq n] [CommRing α]

variable (A : Matrix n n α) (B : Matrix n n α)

theorem inv_kronecker [Fintype m] [DecidableEq m]
    (A : Matrix m m α) (B : Matrix n n α) : (A ⊗ₖ B)⁻¹ = A⁻¹ ⊗ₖ B⁻¹ := by
  -- handle the special cases where either matrix is not invertible
  by_cases hA : IsUnit A.det
  swap
  · cases isEmpty_or_nonempty n
    · subsingleton
    have hAB : ¬IsUnit (A ⊗ₖ B).det := by
      refine mt (fun hAB => ?_) hA
      rw [det_kronecker] at hAB
      exact (isUnit_pow_iff Fintype.card_ne_zero).mp (isUnit_of_mul_isUnit_left hAB)
    rw [Matrix.nonsing_inv_apply_not_isUnit _ hA, zero_kronecker, Matrix.nonsing_inv_apply_not_isUnit _ hAB]
  by_cases hB : IsUnit B.det; swap
  · cases isEmpty_or_nonempty m
    · subsingleton
    have hAB : ¬IsUnit (A ⊗ₖ B).det := by
      refine mt (fun hAB => ?_) hB
      rw [det_kronecker] at hAB
      exact (isUnit_pow_iff Fintype.card_ne_zero).mp (isUnit_of_mul_isUnit_right hAB)
    rw [Matrix.nonsing_inv_apply_not_isUnit _ hB, kronecker_zero, Matrix.nonsing_inv_apply_not_isUnit _ hAB]
  -- otherwise follows trivially from `mul_kronecker_mul`
  · apply Matrix.inv_eq_right_inv
    rw [← mul_kronecker_mul, ← one_kronecker_one, Matrix.mul_nonsing_inv _ hA, Matrix.mul_nonsing_inv _ hB]

