import Mathlib

open scoped Ring Polynomial

variable {R : Type u} [CommRing R]

variable {n G : Type v} [DecidableEq n] [Fintype n]

variable {α β : Type v} [DecidableEq α]

variable {M : Matrix n n R}

theorem derivative_det_one_add_X_smul_aux {n} (M : Matrix (Fin n) (Fin n) R) :
    (derivative <| Matrix.det (1 + (Polynomial.X : R[X]) • M.map Polynomial.C)).eval 0 = Matrix.trace M := by
  induction n with
  | zero => simp
  | succ n IH =>
    rw [det_succ_row_zero, map_sum, eval_finset_sum]
    simp only [add_apply, smul_apply, Matrix.map_apply, smul_eq_mul, X_mul_C, submatrix_add,
      submatrix_smul, Pi.add_apply, Pi.smul_apply, submatrix_map, derivative_mul, map_add,
      derivative_C, zero_mul, derivative_X, mul_one, zero_add, eval_add, eval_mul, eval_C, eval_X,
      mul_zero, add_zero, eval_det_add_X_smul, eval_pow, eval_neg, eval_one]
    rw [Finset.sum_eq_single 0]
    · simp only [Fin.val_zero, pow_zero, derivative_one, eval_zero, one_apply_eq, eval_one,
        mul_one, zero_add, one_mul, Fin.succAbove_zero, submatrix_one _ (Fin.succ_injective _),
        det_one, IH, trace_submatrix_succ]
    · intro i _ hi
      cases n with
      | zero => exact (hi (Subsingleton.elim i 0)).elim
      | succ n =>
        simp only [one_apply_ne' hi, eval_zero, mul_zero, zero_add, zero_mul, add_zero]
        rw [det_eq_zero_of_column_eq_zero 0, eval_zero, mul_zero]
        intro j
        rw [submatrix_apply, Fin.succAbove_of_castSucc_lt, one_apply_ne]
        · exact (bne_iff_ne (a := Fin.succ j) (b := Fin.castSucc 0)).mp rfl
        · rw [Fin.castSucc_zero]; exact lt_of_le_of_ne (Fin.zero_le _) hi.symm
    · exact fun H ↦ (H <| Finset.mem_univ _).elim

