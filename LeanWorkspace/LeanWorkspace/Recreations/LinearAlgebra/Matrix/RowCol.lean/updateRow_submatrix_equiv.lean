import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

variable {M : Matrix m n α} {i : m} {j : n} {b : n → α} {c : m → α}

theorem updateRow_submatrix_equiv [DecidableEq l] [DecidableEq m] (A : Matrix m n α) (i : l)
    (r : o → α) (e : l ≃ m) (f : o ≃ n) :
    Matrix.updateRow (A.submatrix e f) i r = (A.updateRow (e i) fun j => r (f.symm j)).submatrix e f := by
  ext i' j
  simp only [submatrix_apply, Matrix.updateRow_apply, Equiv.apply_eq_iff_eq, Equiv.symm_apply_apply]

