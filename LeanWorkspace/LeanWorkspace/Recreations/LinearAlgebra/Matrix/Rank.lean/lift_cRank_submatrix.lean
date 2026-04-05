import Mathlib

variable {l : Type ul} {m : Type um} {m₀ : Type um₀} {n : Type un} {n₀ : Type un₀} {o : Type uo}

variable {R : Type uR}

variable [Fintype n] [Fintype o]

variable [CommRing R]

theorem lift_cRank_submatrix {n : Type un} (A : Matrix m n R) (em : m₀ ≃ m) (en : n₀ ≃ n) :
    lift.{um} (Matrix.cRank (A.submatrix em en)) = lift.{um₀} (Matrix.cRank A) := (A.lift_cRank_submatrix_le em en).antisymm
    <| by simpa using (Matrix.lift_cRank_submatrix_le (A.reindex em.symm en.symm) em.symm en.symm)

