import Mathlib

variable {l : Type ul} {m : Type um} {m₀ : Type um₀} {n : Type un} {n₀ : Type un₀} {o : Type uo}

variable {R : Type uR}

variable [Fintype n] [Fintype o]

variable [CommRing R]

theorem rank_one [Nontrivial R] [DecidableEq n] :
    Matrix.rank (1 : Matrix n n R) = Fintype.card n := by
  rw [Matrix.rank, mulVecLin_one, LinearMap.range_id, finrank_top, finrank_pi]

