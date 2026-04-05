import Mathlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [FiniteDimensional ℝ E] {L : Submodule ℤ E} [DiscreteTopology L]

variable {ι : Type*} (b : Basis ι ℤ L)

theorem le_norm_of_le_abs_repr {ι : Type*} (b : Module.Basis ι ℤ L) (x : L) (n : ℕ) (i : ι)
    (hi : n ≤ |b.repr x i|) : ZLattice.normBound b * n ≤ ‖x‖ := by
  contrapose! hi
  exact ZLattice.abs_repr_lt_of_norm_lt b x n hi i

