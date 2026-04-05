import Mathlib

variable {l : Type ul} {m : Type um} {m₀ : Type um₀} {n : Type un} {n₀ : Type un₀} {o : Type uo}

variable {R : Type uR}

variable [Fintype n] [Fintype o]

variable [CommRing R]

theorem eRank_zero {m n : Type*} [Nontrivial R] : Matrix.eRank (0 : Matrix m n R) = 0 := by
  simp [Matrix.eRank]

