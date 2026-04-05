import Mathlib

variable {R S T A B C M N O : Type*}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Monoid M] [Monoid N]

theorem coe_algebraMap : ⇑(algebraMap R A[M]) = single 1 ∘ algebraMap R A := rfl

