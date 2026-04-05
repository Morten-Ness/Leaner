import Mathlib

variable {l : Type ul} {m : Type um} {m₀ : Type um₀} {n : Type un} {n₀ : Type un₀} {o : Type uo}

variable {R : Type uR}

variable [Semiring R]

theorem eRank_subsingleton [Subsingleton R] (A : Matrix m n R) : A.eRank = 1 := by
  simp [Matrix.eRank]

