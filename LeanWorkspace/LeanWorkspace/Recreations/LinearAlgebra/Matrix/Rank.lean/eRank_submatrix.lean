import Mathlib

variable {l : Type ul} {m : Type um} {m₀ : Type um₀} {n : Type un} {n₀ : Type un₀} {o : Type uo}

variable {R : Type uR}

variable [Fintype n] [Fintype o]

variable [CommRing R]

theorem eRank_submatrix {n : Type un} (A : Matrix m n R) (em : m₀ ≃ m) (en : n₀ ≃ n) :
    Matrix.eRank (A.submatrix em en) = Matrix.eRank A := by
  simpa [-Matrix.lift_cRank_submatrix] using congr_arg Cardinal.toENat <| A.lift_cRank_submatrix em en

