import Mathlib

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

variable (A : Matrix n n α) (b : n → α)

theorem cramer_subsingleton_apply [Subsingleton n] (A : Matrix n n α) (b : n → α) (i : n) :
    Matrix.cramer A b i = b i := by rw [Matrix.cramer_apply, det_eq_elem_of_subsingleton _ i, updateCol_self]

