import Mathlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable [FiniteDimensional ℝ E] {L : Submodule ℤ E} [DiscreteTopology L]

variable {ι : Type*} (b : Basis ι ℤ L)

theorem summable_norm_sub_zpow (n : ℤ) (hn : n < -Module.finrank ℤ L) (x : E) :
    Summable fun z : L ↦ ‖z - x‖ ^ n := mod_cast ZLattice.summable_norm_sub_rpow L n (mod_cast hn) x

