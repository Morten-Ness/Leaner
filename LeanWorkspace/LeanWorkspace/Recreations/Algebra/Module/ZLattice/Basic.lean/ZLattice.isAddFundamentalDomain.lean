import Mathlib

variable (K : Type*) [NormedField K] [LinearOrder K] [IsStrictOrderedRing K]
  [HasSolidNorm K] [FloorRing K]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace K E] [FiniteDimensional K E]

variable [ProperSpace E] (L : Submodule ℤ E) [DiscreteTopology L]

variable {ι : Type*} [hs : IsZLattice K L] (b : Basis ι ℤ L)

theorem ZLattice.isAddFundamentalDomain {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {L : Submodule ℤ E} [DiscreteTopology L] [IsZLattice ℝ L] [Finite ι]
    (b : Module.Basis ι ℤ L) [MeasurableSpace E] [OpensMeasurableSpace E] (μ : Measure E) :
    IsAddFundamentalDomain L (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) μ := by
  convert ZSpan.isAddFundamentalDomain (b.ofZLatticeBasis ℝ) μ
  all_goals exact (Module.Basis.ofZLatticeBasis_span b ℝ).symm

