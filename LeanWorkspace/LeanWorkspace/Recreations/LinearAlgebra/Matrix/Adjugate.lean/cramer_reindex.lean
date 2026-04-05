import Mathlib

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

variable (A : Matrix n n α) (b : n → α)

theorem cramer_reindex (e : m ≃ n) (A : Matrix m m α) (b : n → α) :
    Matrix.cramer (reindex e e A) b = Matrix.cramer A (b ∘ e) ∘ e.symm := Matrix.cramer_submatrix_equiv _ _ _

