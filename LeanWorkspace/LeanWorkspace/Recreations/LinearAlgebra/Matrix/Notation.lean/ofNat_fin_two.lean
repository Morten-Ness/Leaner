import Mathlib

variable {α : Type u} {o n m : ℕ} {m' : Type uₘ} {n' : Type uₙ} {o' : Type uₒ}

variable (a b : ℕ)

variable [AddMonoidWithOne α]

theorem ofNat_fin_two (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : Matrix (Fin 2) (Fin 2) α) =
      !![ofNat(n), 0; 0, ofNat(n)] := Matrix.natCast_fin_two _

