import Mathlib

variable {l : Type ul} {m : Type um} {m₀ : Type um₀} {n : Type un} {n₀ : Type un₀} {o : Type uo}

variable {R : Type uR}

variable [Fintype n] [Fintype o]

variable [CommRing R]

theorem rank_le_card_height [Fintype m] [Nontrivial R] (A : Matrix m n R) :
    A.rank ≤ Fintype.card m := by
  exact (Submodule.finrank_le _).trans (finrank_pi R).le

