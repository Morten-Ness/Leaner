import Mathlib

variable {l : Type ul} {m : Type um} {m₀ : Type um₀} {n : Type un} {n₀ : Type un₀} {o : Type uo}

variable {R : Type uR}

variable [Fintype n] [Fintype o]

variable [CommRing R]

theorem rank_le_width [Nontrivial R] {m n : ℕ} (A : Matrix (Fin m) (Fin n) R) :
    A.rank ≤ n := A.rank_le_card_width.trans <| (Fintype.card_fin n).le

