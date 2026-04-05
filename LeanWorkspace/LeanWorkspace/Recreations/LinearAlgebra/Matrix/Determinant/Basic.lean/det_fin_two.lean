import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_fin_two (A : Matrix (Fin 2) (Fin 2) R) : Matrix.det A = A 0 0 * A 1 1 - A 0 1 * A 1 0 := by
  simp only [Matrix.det_succ_row_zero, Matrix.det_unique, Fin.default_eq_zero, submatrix_apply,
    Fin.succ_zero_eq_one, Fin.sum_univ_succ, Fin.val_zero, Fin.zero_succAbove, univ_unique,
    Fin.val_succ, Fin.val_eq_zero, Fin.succ_succAbove_zero, sum_singleton]
  ring

