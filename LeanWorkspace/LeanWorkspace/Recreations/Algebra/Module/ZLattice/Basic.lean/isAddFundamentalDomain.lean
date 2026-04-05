import Mathlib

variable {E ι : Type*}

variable [NormedAddCommGroup E] [NormedSpace ℝ E] (b : Basis ι ℝ E)

theorem isAddFundamentalDomain [Finite ι] [MeasurableSpace E] [OpensMeasurableSpace E]
    (μ : Measure E) :
    IsAddFundamentalDomain (span ℤ (Set.range b)) (ZSpan.fundamentalDomain b) μ := by
  cases nonempty_fintype ι
  exact IsAddFundamentalDomain.mk' (nullMeasurableSet (ZSpan.fundamentalDomain_measurableSet b))
    fun x => ZSpan.exist_unique_vadd_mem_fundamentalDomain b x

