import Mathlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [FiniteDimensional ℝ E] {L : Submodule ℤ E} [DiscreteTopology L]

variable {ι : Type*} (b : Basis ι ℤ L)

theorem tsumNormRPowBound_pos : 0 < ZLattice.tsumNormRPowBound L := (ZLattice.exists_finsetSum_norm_rpow_le_tsum L).choose_spec.1

