import Mathlib

variable {l : Type ul} {m : Type um} {m₀ : Type um₀} {n : Type un} {n₀ : Type un₀} {o : Type uo}

variable {R : Type uR}

variable [Fintype n] [Fintype o]

variable [CommRing R]

theorem cRank_reindex {m₀ : Type um} {n : Type un} (A : Matrix m n R) (em : m ≃ m₀) (en : n ≃ n₀) :
    Matrix.cRank (A.reindex em en) = Matrix.cRank A := Matrix.cRank_submatrix ..

