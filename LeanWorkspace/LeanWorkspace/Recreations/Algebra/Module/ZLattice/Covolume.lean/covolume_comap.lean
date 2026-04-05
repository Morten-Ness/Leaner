import Mathlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

variable [MeasurableSpace E] [BorelSpace E]

variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

variable (μ : Measure E := by volume_tac) [Measure.IsAddHaarMeasure μ]

set_option backward.privateInPublic true in
theorem covolume_comap {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] (ν : Measure F := by volume_tac) [Measure.IsAddHaarMeasure ν]
    {e : F ≃L[ℝ] E} (he : MeasurePreserving e ν μ) :
    ZLattice.covolume (ZLattice.comap ℝ L e.toLinearMap) ν = ZLattice.covolume L μ := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ (isAddFundamentalDomain (Free.chooseBasis ℤ L) μ),
    ZLattice.covolume_eq_measure_fundamentalDomain _ _ ((isAddFundamentalDomain
    ((Free.chooseBasis ℤ L).ofZLatticeComap ℝ L e.toLinearEquiv) ν)), ← he.measureReal_preimage
    (fundamentalDomain_measurableSet _).nullMeasurableSet, ← e.image_symm_eq_preimage,
    ← e.symm.coe_toLinearEquiv, map_fundamentalDomain]
  congr!
  ext; simp

