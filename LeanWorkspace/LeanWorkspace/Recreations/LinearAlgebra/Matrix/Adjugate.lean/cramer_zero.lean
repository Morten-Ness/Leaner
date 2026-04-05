import Mathlib

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

variable (A : Matrix n n α) (b : n → α)

theorem cramer_zero [Nontrivial n] : Matrix.cramer (0 : Matrix n n α) = 0 := by
  ext i j
  obtain ⟨j', hj'⟩ : ∃ j', j' ≠ j := exists_ne j
  apply det_eq_zero_of_column_eq_zero j'
  simp [updateCol_ne hj']

