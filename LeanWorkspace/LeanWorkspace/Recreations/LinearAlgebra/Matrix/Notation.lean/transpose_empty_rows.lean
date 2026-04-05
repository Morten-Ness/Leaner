import Mathlib

variable {α : Type u} {o n m : ℕ} {m' : Type uₘ} {n' : Type uₙ} {o' : Type uₒ}

variable (a b : ℕ)

theorem transpose_empty_rows (A : Matrix m' (Fin 0) α) : Aᵀ = of ![] := empty_eq _

