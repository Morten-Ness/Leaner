import Mathlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

variable [MeasurableSpace E] [BorelSpace E]

variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

variable (μ : Measure E := by volume_tac) [Measure.IsAddHaarMeasure μ]

set_option backward.privateInPublic true in
theorem covolume_ne_zero : ZLattice.covolume L μ ≠ 0 := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain L μ (isAddFundamentalDomain (Free.chooseBasis ℤ L) μ),
    measureReal_ne_zero_iff (ne_of_lt _)]
  · exact measure_fundamentalDomain_ne_zero _
  · exact Bornology.IsBounded.measure_lt_top (fundamentalDomain_isBounded _)

