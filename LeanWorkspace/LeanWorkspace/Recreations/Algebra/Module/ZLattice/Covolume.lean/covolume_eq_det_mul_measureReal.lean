import Mathlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

variable [MeasurableSpace E] [BorelSpace E]

variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

variable (μ : Measure E := by volume_tac) [Measure.IsAddHaarMeasure μ]

set_option backward.privateInPublic true in
theorem covolume_eq_det_mul_measureReal {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℤ L)
    (b₀ : Module.Basis ι ℝ E) :
    ZLattice.covolume L μ = |b₀.det ((↑) ∘ b)| * μ.real (fundamentalDomain b₀) := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain L μ (isAddFundamentalDomain b μ),
    measureReal_fundamentalDomain _ _ b₀,
    measureReal_congr (fundamentalDomain_ae_parallelepiped b₀ μ)]
  congr
  ext
  exact b.ofZLatticeBasis_apply ℝ L _

