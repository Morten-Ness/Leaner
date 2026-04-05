import Mathlib

variable {α : Type u} {o n m : ℕ} {m' : Type uₘ} {n' : Type uₙ} {o' : Type uₒ}

variable (a b : ℕ)

variable [AddMonoidWithOne α]

theorem ofNat_fin_three (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : Matrix (Fin 3) (Fin 3) α) =
      !![ofNat(n), 0, 0; 0, ofNat(n), 0; 0, 0, ofNat(n)] := Matrix.natCast_fin_three _

