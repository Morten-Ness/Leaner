import Mathlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [FiniteDimensional ℝ E] {L : Submodule ℤ E} [DiscreteTopology L]

variable {ι : Type*} (b : Basis ι ℤ L)

theorem normBound_pos {ι : Type*} (b : Module.Basis ι ℤ L) : 0 < ZLattice.normBound b := (ZLattice.exists_forall_abs_repr_le_norm b).choose_spec.1

