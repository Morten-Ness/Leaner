import Mathlib

variable {l : Type ul} {m : Type um} {m₀ : Type um₀} {n : Type un} {n₀ : Type un₀} {o : Type uo}

variable {R : Type uR}

variable [Fintype n] [Fintype o]

variable [CommRing R]

theorem rank_reindex [Fintype n₀] (em : m ≃ m₀) (en : n ≃ n₀) (A : Matrix m n R) :
    Matrix.rank (A.reindex em en) = Matrix.rank A := by
  rw [Matrix.rank, Matrix.rank, mulVecLin_reindex, LinearMap.range_comp, LinearMap.range_comp,
    LinearEquiv.range, Submodule.map_top, LinearEquiv.finrank_map_eq]

