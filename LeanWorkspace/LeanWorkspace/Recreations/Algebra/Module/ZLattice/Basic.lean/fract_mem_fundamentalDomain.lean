import Mathlib

variable {E ι : Type*}

variable {K : Type*} [NormedField K]

variable [NormedAddCommGroup E] [NormedSpace K E]

variable (b : Basis ι K E)

variable [LinearOrder K]

variable [IsStrictOrderedRing K]

variable [FloorRing K]

variable [Fintype ι]

theorem fract_mem_fundamentalDomain (x : E) : ZSpan.fract b x ∈ ZSpan.fundamentalDomain b := ZSpan.fract_eq_self.mp (ZSpan.fract_fract b _)

