import Mathlib

variable {l : Type ul} {m : Type um} {m₀ : Type um₀} {n : Type un} {n₀ : Type un₀} {o : Type uo}

variable {R : Type uR}

variable [Fintype n] [Fintype o]

variable [CommRing R]

omit [Fintype n] in
theorem rank_submatrix_le [Nontrivial R] [Fintype m] [Fintype m₀] (f : n₀ → n) (e : m₀ ≃ m)
    (A : Matrix n m R) : Matrix.rank (A.submatrix f e) ≤ Matrix.rank A := by
  rw [Matrix.rank, Matrix.rank, mulVecLin_submatrix, LinearMap.range_comp, LinearMap.range_comp,
    show LinearMap.funLeft R R e.symm = LinearEquiv.funCongrLeft R R e.symm from rfl,
    LinearEquiv.range, Submodule.map_top]
  exact Submodule.finrank_map_le _ _

