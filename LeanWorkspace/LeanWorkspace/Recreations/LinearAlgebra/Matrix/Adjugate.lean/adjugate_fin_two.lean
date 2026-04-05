import Mathlib

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

theorem adjugate_fin_two (A : Matrix (Fin 2) (Fin 2) α) :
    Matrix.adjugate A = !![A 1 1, -A 0 1; -A 1 0, A 0 0] := by
  ext i j
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  fin_cases i <;> fin_cases j <;> simp

