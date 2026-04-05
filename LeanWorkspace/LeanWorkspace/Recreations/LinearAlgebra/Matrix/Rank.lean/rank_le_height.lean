import Mathlib

variable {l : Type ul} {m : Type um} {m₀ : Type um₀} {n : Type un} {n₀ : Type un₀} {o : Type uo}

variable {R : Type uR}

variable [Fintype n] [Fintype o]

variable [CommRing R]

theorem rank_le_height [Nontrivial R] {m n : ℕ} (A : Matrix (Fin m) (Fin n) R) :
    A.rank ≤ m := A.rank_le_card_height.trans <| (Fintype.card_fin m).le

