import Mathlib

variable {E ι : Type*}

variable [NormedAddCommGroup E] [NormedSpace ℝ E] (b : Basis ι ℝ E)

theorem volume_fundamentalDomain [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ (ι → ℝ)) :
    volume (ZSpan.fundamentalDomain b) = ENNReal.ofReal |(Matrix.of b).det| := by
  rw [ZSpan.measure_fundamentalDomain b volume (b₀ := Pi.basisFun ℝ ι), ZSpan.fundamentalDomain_pi_basisFun,
    volume_pi, Measure.pi_pi, Real.volume_Ico, sub_zero, ENNReal.ofReal_one, Finset.prod_const_one,
    mul_one, ← Matrix.det_transpose]
  rfl

