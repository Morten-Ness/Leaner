import Mathlib

variable {K : Type*}

variable [DivisionSemiring K]

theorem smul_def (q : ℚ≥0) (a : K) : q • a = q * a := DivisionSemiring.nnqsmul_def q a

