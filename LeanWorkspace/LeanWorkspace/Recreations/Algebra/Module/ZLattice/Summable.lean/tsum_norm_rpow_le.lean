import Mathlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [FiniteDimensional ℝ E] {L : Submodule ℤ E} [DiscreteTopology L]

variable {ι : Type*} (b : Basis ι ℤ L)

theorem tsum_norm_rpow_le (r : ℝ) (hr : r < -Module.finrank ℤ L) :
    ∑' z : L, ‖z‖ ^ r ≤
      ZLattice.tsumNormRPowBound L ^ r * ∑' k : ℕ, (k : ℝ) ^ (Module.finrank ℤ L - 1 + r) := Summable.tsum_le_of_sum_le (ZLattice.summable_norm_rpow L r hr) (ZLattice.tsumNormRPowBound_spec L r hr)

