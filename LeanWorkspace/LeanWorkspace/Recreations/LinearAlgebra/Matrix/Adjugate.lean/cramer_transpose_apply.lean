import Mathlib

variable {m : Type u} {n : Type v} {α : Type w}

variable [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m] [CommRing α]

variable (A : Matrix n n α) (b : n → α)

theorem cramer_transpose_apply (i : n) : Matrix.cramer Aᵀ b i = (A.updateRow i b).det := by
  rw [Matrix.cramer_apply, updateCol_transpose, det_transpose]

