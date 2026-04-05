import Mathlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [FiniteDimensional ℝ E] {L : Submodule ℤ E} [DiscreteTopology L]

variable {ι : Type*} (b : Basis ι ℤ L)

theorem abs_repr_le {ι : Type*} (b : Module.Basis ι ℤ L) (x : L) (i : ι) :
    |b.repr x i| ≤ (ZLattice.normBound b)⁻¹ * ‖x‖ := by
  rw [le_inv_mul_iff₀ (ZLattice.normBound_pos b)]
  exact ZLattice.normBound_spec b x i

