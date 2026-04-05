import Mathlib

variable {α : Type u} {o n m : ℕ} {m' : Type uₘ} {n' : Type uₙ} {o' : Type uₒ}

variable (a b : ℕ)

variable {ι : Type*}

theorem replicateCol_empty (v : Fin 0 → α) : replicateCol ι v = vecEmpty := empty_eq _

