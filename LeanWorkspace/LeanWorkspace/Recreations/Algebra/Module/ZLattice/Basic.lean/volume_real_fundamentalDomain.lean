import Mathlib

variable {E ι : Type*}

variable [NormedAddCommGroup E] [NormedSpace ℝ E] (b : Basis ι ℝ E)

theorem volume_real_fundamentalDomain [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ (ι → ℝ)) :
    volume.real (ZSpan.fundamentalDomain b) = |(Matrix.of b).det| := by
  simp [measureReal_def]

