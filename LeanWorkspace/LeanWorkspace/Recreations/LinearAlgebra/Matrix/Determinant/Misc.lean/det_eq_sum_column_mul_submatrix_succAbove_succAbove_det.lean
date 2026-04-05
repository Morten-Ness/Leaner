import Mathlib

variable {R : Type*} [CommRing R]

theorem det_eq_sum_column_mul_submatrix_succAbove_succAbove_det {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (i₀ j₀ : Fin (n + 1))
    (hv : ∀ j ≠ j₀, ∑ i, M i j = 0) :
    M.det = (-1) ^ (i₀ + j₀ : ℕ) *
      (∑ i, M i j₀) * (M.submatrix (Fin.succAbove i₀) (Fin.succAbove j₀)).det := by
  rw [← one_smul R M.det, ← Matrix.det_updateRow_sum _ i₀ (fun _ ↦ 1), Matrix.det_succ_row _ i₀]
  simp only [updateRow_apply, if_true, one_smul, submatrix_updateRow_succAbove, Finset.sum_apply]
  rw [Fintype.sum_eq_add_sum_subtype_ne _ j₀]
  conv_lhs =>
    enter [2, 2, i]
    rw [hv _ i.prop, mul_zero, zero_mul]
  simp [Finset.sum_const_zero, add_zero]

