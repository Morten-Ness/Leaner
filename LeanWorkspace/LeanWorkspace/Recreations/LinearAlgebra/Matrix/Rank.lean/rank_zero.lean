import Mathlib

variable {l : Type ul} {m : Type um} {m₀ : Type um₀} {n : Type un} {n₀ : Type un₀} {o : Type uo}

variable {R : Type uR}

variable [Fintype n] [Fintype o]

variable [CommRing R]

theorem rank_zero [Nontrivial R] : Matrix.rank (0 : Matrix m n R) = 0 := by
  rw [Matrix.rank, mulVecLin_zero, LinearMap.range_zero, finrank_bot]

