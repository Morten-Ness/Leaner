import Mathlib

variable {G : Type*}

variable [Mul G]

variable {R : Type*}

theorem IsRightRegular.all [Mul R] [IsRightCancelMul R] (g : R) : IsRightRegular g := (isRightCancelMul_iff R).mp ‹_› _

