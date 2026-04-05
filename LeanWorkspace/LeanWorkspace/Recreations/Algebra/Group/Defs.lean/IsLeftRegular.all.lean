import Mathlib

variable {G : Type*}

variable [Mul G]

variable {R : Type*}

theorem IsLeftRegular.all [Mul R] [IsLeftCancelMul R] (g : R) : IsLeftRegular g := (isLeftCancelMul_iff R).mp ‹_› _

