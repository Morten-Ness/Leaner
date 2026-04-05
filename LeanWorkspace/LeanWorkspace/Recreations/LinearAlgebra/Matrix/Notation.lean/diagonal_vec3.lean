import Mathlib

variable {α : Type u} {o n m : ℕ} {m' : Type uₘ} {n' : Type uₙ} {o' : Type uₒ}

variable (a b : ℕ)

variable [Zero α]

theorem diagonal_vec3 (a b c : α) :
    diagonal ![a, b, c] = !![a, 0, 0; 0, b, 0; 0, 0, c] := Matrix.diagonal_fin_three ![a, b, c]

