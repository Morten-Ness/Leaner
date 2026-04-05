import Mathlib

variable {l : Type ul} {m : Type um} {m₀ : Type um₀} {n : Type un} {n₀ : Type un₀} {o : Type uo}

variable {R : Type uR}

variable [Fintype n] [Fintype o]

variable [CommRing R]

theorem cRank_submatrix {m₀ : Type um} {n : Type un} (A : Matrix m n R) (em : m₀ ≃ m)
    (en : n₀ ≃ n) : Matrix.cRank (A.submatrix em en) = Matrix.cRank A := by
  simpa [-Matrix.lift_cRank_submatrix] using A.lift_cRank_submatrix em en

