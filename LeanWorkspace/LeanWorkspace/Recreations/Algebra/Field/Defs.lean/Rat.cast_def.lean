import Mathlib

variable {K : Type*}

variable [DivisionRing K]

theorem cast_def (q : ℚ) : (q : K) = q.num / q.den := DivisionRing.ratCast_def _

