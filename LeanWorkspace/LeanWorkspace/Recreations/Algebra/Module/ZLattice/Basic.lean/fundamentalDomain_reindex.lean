import Mathlib

variable {E ι : Type*}

variable {K : Type*} [NormedField K]

variable [NormedAddCommGroup E] [NormedSpace K E]

variable (b : Basis ι K E)

variable [LinearOrder K]

theorem fundamentalDomain_reindex {ι' : Type*} (e : ι ≃ ι') :
    ZSpan.fundamentalDomain (b.reindex e) = ZSpan.fundamentalDomain b := by
  ext
  simp [e.forall_congr_left]

