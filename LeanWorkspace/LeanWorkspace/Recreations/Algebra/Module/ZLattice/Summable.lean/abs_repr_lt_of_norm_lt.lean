import Mathlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [FiniteDimensional ℝ E] {L : Submodule ℤ E} [DiscreteTopology L]

variable {ι : Type*} (b : Basis ι ℤ L)

theorem abs_repr_lt_of_norm_lt {ι : Type*} (b : Module.Basis ι ℤ L) (x : L) (n : ℕ)
    (hxn : ‖x‖ < ZLattice.normBound b * n) (i : ι) : |b.repr x i| < n := by
  refine Int.cast_lt.mp ((ZLattice.abs_repr_le b x i).trans_lt ?_)
  rwa [inv_mul_lt_iff₀ (ZLattice.normBound_pos b)]

