import Mathlib

variable {E ι : Type*}

variable [NormedAddCommGroup E] [NormedSpace ℝ E] (b : Basis ι ℝ E)

theorem measureReal_fundamentalDomain
    [Fintype ι] [DecidableEq ι] [MeasurableSpace E] (μ : Measure E)
    [BorelSpace E] [Measure.IsAddHaarMeasure μ] (b₀ : Module.Basis ι ℝ E) :
    μ.real (ZSpan.fundamentalDomain b) = |b₀.det b| * μ.real (ZSpan.fundamentalDomain b₀) := by
  simp [measureReal_def, ZSpan.measure_fundamentalDomain b μ b₀]

