import Mathlib

variable {l : Type ul} {m : Type um} {m₀ : Type um₀} {n : Type un} {n₀ : Type un₀} {o : Type uo}

variable {R : Type uR}

variable [Fintype n] [Fintype o]

variable [CommRing R]

theorem lift_cRank_reindex {n : Type un} (A : Matrix m n R) (em : m ≃ m₀) (en : n ≃ n₀) :
    lift.{um} (Matrix.cRank (A.reindex em en)) = lift.{um₀} (Matrix.cRank A) := Matrix.lift_cRank_submatrix ..

