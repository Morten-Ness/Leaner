import Mathlib

variable {α : Type u} {o n m : ℕ} {m' : Type uₘ} {n' : Type uₙ} {o' : Type uₒ}

variable (a b : ℕ)

variable [Zero α]

theorem diagonal_fin_three (d : Fin 3 → α) :
    diagonal d = !![d 0, 0, 0; 0, d 1, 0; 0, 0, d 2] := by
  simp [← Matrix.ext_iff, Fin.forall_fin_succ]

