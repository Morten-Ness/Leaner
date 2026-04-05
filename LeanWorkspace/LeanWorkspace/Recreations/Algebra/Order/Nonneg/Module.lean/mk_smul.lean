import Mathlib

variable {R S M : Type*}

variable [Semiring R] [PartialOrder R]

variable [SMul R S]

theorem mk_smul (a) (ha) (x : S) : (⟨a, ha⟩ : R≥0) • x = a • x := rfl

