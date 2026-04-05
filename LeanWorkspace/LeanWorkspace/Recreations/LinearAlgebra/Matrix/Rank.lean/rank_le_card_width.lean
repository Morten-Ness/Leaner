import Mathlib

variable {l : Type ul} {m : Type um} {m₀ : Type um₀} {n : Type un} {n₀ : Type un₀} {o : Type uo}

variable {R : Type uR}

variable [Fintype n] [Fintype o]

variable [CommRing R]

theorem rank_le_card_width [Nontrivial R] (A : Matrix m n R) :
    A.rank ≤ Fintype.card n := by
  exact A.mulVecLin.finrank_range_le.trans_eq (finrank_pi _)

