import Mathlib

variable {E ι : Type*}

variable [NormedAddCommGroup E] [NormedSpace ℝ E] (b : Basis ι ℝ E)

theorem measure_fundamentalDomain [Fintype ι] [DecidableEq ι] [MeasurableSpace E] (μ : Measure E)
    [BorelSpace E] [Measure.IsAddHaarMeasure μ] (b₀ : Module.Basis ι ℝ E) :
    μ (ZSpan.fundamentalDomain b) = ENNReal.ofReal |b₀.det b| * μ (ZSpan.fundamentalDomain b₀) := by
  have : FiniteDimensional ℝ E := b.finiteDimensional_of_finite
  convert μ.addHaar_preimage_linearEquiv (b.equiv b₀ (Equiv.refl ι)) (ZSpan.fundamentalDomain b₀)
  · rw [Set.eq_preimage_iff_image_eq (LinearEquiv.bijective _), ZSpan.map_fundamentalDomain,
      Module.Basis.map_equiv, Equiv.refl_symm, Module.Basis.reindex_refl]
  · simp

