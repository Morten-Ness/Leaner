import Mathlib

variable {K : Type*}

variable [DivisionRing K]

theorem smul_def (a : ℚ) (x : K) : a • x = ↑a * x := DivisionRing.qsmul_def a x

