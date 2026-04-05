import Mathlib

variable {E ι : Type*}

variable [NormedAddCommGroup E] [NormedSpace ℝ E] (b : Basis ι ℝ E)

theorem measure_fundamentalDomain_ne_zero [Finite ι] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [Measure.IsAddHaarMeasure μ] :
    μ (ZSpan.fundamentalDomain b) ≠ 0 := by
  convert (ZSpan.isAddFundamentalDomain b μ).measure_ne_zero (NeZero.ne μ)
  exact inferInstanceAs <| VAddInvariantMeasure (span ℤ (Set.range b)).toAddSubgroup E μ

