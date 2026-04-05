import Mathlib

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

variable (A : Matrix n n α) (b : n → α)

theorem cramer_is_linear : IsLinearMap α (Matrix.cramerMap A) := by
  constructor <;> intros <;> ext i
  · apply (Matrix.cramerMap_is_linear A i).1
  · apply (Matrix.cramerMap_is_linear A i).2

