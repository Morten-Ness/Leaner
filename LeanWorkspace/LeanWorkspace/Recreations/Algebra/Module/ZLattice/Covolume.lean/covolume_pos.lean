import Mathlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

variable [MeasurableSpace E] [BorelSpace E]

variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

variable (μ : Measure E := by volume_tac) [Measure.IsAddHaarMeasure μ]

set_option backward.privateInPublic true in
theorem covolume_pos : 0 < ZLattice.covolume L μ := lt_of_le_of_ne ENNReal.toReal_nonneg (ZLattice.covolume_ne_zero L μ).symm

