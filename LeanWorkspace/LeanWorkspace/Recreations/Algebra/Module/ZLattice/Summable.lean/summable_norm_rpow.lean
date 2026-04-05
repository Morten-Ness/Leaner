import Mathlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [FiniteDimensional ℝ E] {L : Submodule ℤ E} [DiscreteTopology L]

variable {ι : Type*} (b : Basis ι ℤ L)

theorem summable_norm_rpow (r : ℝ) (hr : r < -Module.finrank ℤ L) :
    Summable fun z : L ↦ ‖z‖ ^ r := summable_of_sum_le (fun _ ↦ by positivity) (ZLattice.tsumNormRPowBound_spec L r hr)

