import Mathlib

variable {K : Type*}

variable [DivisionSemiring K]

theorem cast_def (q : ℚ≥0) : (q : K) = q.num / q.den := DivisionSemiring.nnratCast_def _

