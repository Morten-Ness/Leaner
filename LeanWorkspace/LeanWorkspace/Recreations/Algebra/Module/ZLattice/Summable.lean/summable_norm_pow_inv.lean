import Mathlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [FiniteDimensional ℝ E] {L : Submodule ℤ E} [DiscreteTopology L]

variable {ι : Type*} (b : Basis ι ℤ L)

theorem summable_norm_pow_inv (n : ℕ) (hn : Module.finrank ℤ L < n) :
    Summable fun z : L ↦ ‖z‖⁻¹ ^ n := by
  simpa using ZLattice.summable_norm_sub_inv_pow L n hn 0

