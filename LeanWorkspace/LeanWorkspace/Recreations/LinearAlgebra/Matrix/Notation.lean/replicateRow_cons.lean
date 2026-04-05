import Mathlib

variable {α : Type u} {o n m : ℕ} {m' : Type uₘ} {n' : Type uₙ} {o' : Type uₒ}

variable (a b : ℕ)

variable {ι : Type*}

theorem replicateRow_cons (x : α) (u : Fin m → α) :
    replicateRow ι (vecCons x u) = of fun _ => vecCons x u := rfl

