import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

variable {M : Matrix m n α} {i : m} {j : n} {b : n → α} {c : m → α}

theorem submatrix_updateCol_equiv [DecidableEq o] [DecidableEq n] (A : Matrix m n α) (j : n)
    (c : m → α) (e : l ≃ m) (f : o ≃ n) : (A.updateCol j c).submatrix e f =
    Matrix.updateCol (A.submatrix e f) (f.symm j) fun i => c (e i) := Eq.trans (by simp_rw [Equiv.apply_symm_apply]) (Matrix.updateCol_submatrix_equiv A _ _ e f).symm

