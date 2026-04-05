import Mathlib

variable {E ι : Type*}

variable {K : Type*} [NormedField K]

variable [NormedAddCommGroup E] [NormedSpace K E]

variable (b : Basis ι K E)

variable [LinearOrder K]

variable [IsStrictOrderedRing K]

theorem fundamentalDomain_pi_basisFun [Fintype ι] :
    ZSpan.fundamentalDomain (Pi.basisFun ℝ ι) = Set.pi Set.univ fun _ : ι ↦ Set.Ico (0 : ℝ) 1 := by
  ext; simp

