import Mathlib

variable {R S M : Type*}

variable [Semiring R] [PartialOrder R]

variable [SMul R S]

theorem coe_smul (a : R≥0) (x : S) : (a : R) • x = a • x := rfl

