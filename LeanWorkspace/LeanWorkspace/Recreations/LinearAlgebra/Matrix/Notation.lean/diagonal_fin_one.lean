import Mathlib

variable {α : Type u} {o n m : ℕ} {m' : Type uₘ} {n' : Type uₙ} {o' : Type uₒ}

variable (a b : ℕ)

variable [Zero α]

theorem diagonal_fin_one (d : Fin 1 → α) : diagonal d = !![d 0] := by
  simp [← Matrix.ext_iff]

