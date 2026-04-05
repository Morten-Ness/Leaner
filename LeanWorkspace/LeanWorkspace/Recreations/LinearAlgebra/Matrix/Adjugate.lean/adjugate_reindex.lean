import Mathlib

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

theorem adjugate_reindex (e : m ≃ n) (A : Matrix m m α) :
    Matrix.adjugate (reindex e e A) = reindex e e (Matrix.adjugate A) := Matrix.adjugate_submatrix_equiv_self _ _

