import Mathlib

variable {l : Type ul} {m : Type um} {m₀ : Type um₀} {n : Type un} {n₀ : Type un₀} {o : Type uo}

variable {R : Type uR}

variable [Fintype n] [Fintype o]

variable [CommRing R]

theorem rank_submatrix [Fintype n₀] (A : Matrix m n R) (em : m₀ ≃ m) (en : n₀ ≃ n) :
    Matrix.rank (A.submatrix em en) = Matrix.rank A := by
  simpa only [reindex_apply] using Matrix.rank_reindex em.symm en.symm A

