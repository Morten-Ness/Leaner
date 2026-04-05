import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

variable {M : Matrix m n α} {i : m} {j : n} {b : n → α} {c : m → α}

theorem updateRow_reindex [DecidableEq l] [DecidableEq m] (A : Matrix m n α) (i : l) (r : o → α)
    (e : m ≃ l) (f : n ≃ o) :
    Matrix.updateRow (reindex e f A) i r = reindex e f (A.updateRow (e.symm i) fun j => r (f j)) := Matrix.updateRow_submatrix_equiv _ _ _ _ _

