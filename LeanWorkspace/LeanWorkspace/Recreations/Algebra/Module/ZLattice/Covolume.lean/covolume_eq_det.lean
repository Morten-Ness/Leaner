import Mathlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

variable [MeasurableSpace E] [BorelSpace E]

variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

variable (μ : Measure E := by volume_tac) [Measure.IsAddHaarMeasure μ]

theorem covolume_eq_det {ι : Type*} [Fintype ι] [DecidableEq ι] (L : Submodule ℤ (ι → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L] (b : Module.Basis ι ℤ L) :
    ZLattice.covolume L = |(Matrix.of ((↑) ∘ b)).det| := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain L volume (isAddFundamentalDomain b volume),
    volume_real_fundamentalDomain]
  congr
  ext1
  exact b.ofZLatticeBasis_apply ℝ L _

