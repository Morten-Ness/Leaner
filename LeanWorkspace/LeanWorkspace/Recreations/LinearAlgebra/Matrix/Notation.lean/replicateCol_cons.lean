import Mathlib

variable {α : Type u} {o n m : ℕ} {m' : Type uₘ} {n' : Type uₙ} {o' : Type uₒ}

variable (a b : ℕ)

variable {ι : Type*}

theorem replicateCol_cons (x : α) (u : Fin m → α) :
    replicateCol ι (vecCons x u) = of (vecCons (fun _ => x) (replicateCol ι u)) := by
  ext i j
  refine Fin.cases ?_ ?_ i <;> simp

