import Mathlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [FiniteDimensional ℝ E] {L : Submodule ℤ E} [DiscreteTopology L]

variable {ι : Type*} (b : Basis ι ℤ L)

theorem summable_norm_zpow (n : ℤ) (hn : n < -Module.finrank ℤ L) :
    Summable fun z : L ↦ ‖z‖ ^ n := by
  simpa using ZLattice.summable_norm_sub_zpow L n hn 0

