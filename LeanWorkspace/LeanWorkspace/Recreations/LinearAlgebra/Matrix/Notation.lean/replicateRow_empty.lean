import Mathlib

variable {α : Type u} {o n m : ℕ} {m' : Type uₘ} {n' : Type uₙ} {o' : Type uₒ}

variable (a b : ℕ)

variable {ι : Type*}

theorem replicateRow_empty : replicateRow ι (vecEmpty : Fin 0 → α) = of fun _ => vecEmpty := rfl

