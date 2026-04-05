import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

variable {M : Matrix m n α} {i : m} {j : n} {b : n → α} {c : m → α}

theorem submatrix_updateRow_equiv [DecidableEq l] [DecidableEq m] (A : Matrix m n α) (i : m)
    (r : n → α) (e : l ≃ m) (f : o ≃ n) :
    (A.updateRow i r).submatrix e f = Matrix.updateRow (A.submatrix e f) (e.symm i) fun i => r (f i) := Eq.trans (by simp_rw [Equiv.apply_symm_apply]) (Matrix.updateRow_submatrix_equiv A _ _ e f).symm

