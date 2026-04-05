import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

theorem det_eq_of_forall_col_eq_smul_add_pred {n : ℕ} {A B : Matrix (Fin (n + 1)) (Fin (n + 1)) R}
    (c : Fin n → R) (A_zero : ∀ i, A i 0 = B i 0)
    (A_succ : ∀ (i) (j : Fin n), A i j.succ = B i j.succ + c j * A i (Fin.castSucc j)) :
    Matrix.det A = Matrix.det B := by
  rw [← Matrix.det_transpose A, ← Matrix.det_transpose B]
  exact Matrix.det_eq_of_forall_row_eq_smul_add_pred c A_zero fun i j => A_succ j i

