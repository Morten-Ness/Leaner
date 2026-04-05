import Mathlib

variable {α : Type u} {o n m : ℕ} {m' : Type uₘ} {n' : Type uₙ} {o' : Type uₒ}

variable (a b : ℕ)

variable [Zero α]

theorem diagonal_vec2 (a b : α) : diagonal ![a, b] = !![a, 0; 0, b] := Matrix.diagonal_fin_two ![a, b]

