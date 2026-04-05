import Mathlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [FiniteDimensional ℝ E] {L : Submodule ℤ E} [DiscreteTopology L]

variable {ι : Type*} (b : Basis ι ℤ L)

theorem summable_norm_sub_inv_pow (n : ℕ) (hn : Module.finrank ℤ L < n) (x : E) :
    Summable fun z : L ↦ ‖z - x‖⁻¹ ^ n := by
  simpa using ZLattice.summable_norm_sub_zpow L (-n) (by gcongr) x

