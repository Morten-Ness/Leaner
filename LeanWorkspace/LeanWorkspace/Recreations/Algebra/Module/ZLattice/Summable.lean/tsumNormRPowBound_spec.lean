import Mathlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [FiniteDimensional ℝ E] {L : Submodule ℤ E} [DiscreteTopology L]

variable {ι : Type*} (b : Basis ι ℤ L)

theorem tsumNormRPowBound_spec (r : ℝ) (h : r < -Module.finrank ℤ L) (s : Finset L) :
    ∑ z ∈ s, ‖z‖ ^ r ≤
      ZLattice.tsumNormRPowBound L ^ r * ∑' k : ℕ, (k : ℝ) ^ (Module.finrank ℤ L - 1 + r) := (ZLattice.exists_finsetSum_norm_rpow_le_tsum L).choose_spec.2 r h s

