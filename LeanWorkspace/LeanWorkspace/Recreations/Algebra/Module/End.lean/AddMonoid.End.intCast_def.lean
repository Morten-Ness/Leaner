import Mathlib

variable {R S M M₂ : Type*}

variable (R M) [Semiring R] [AddCommGroup M]

theorem AddMonoid.End.intCast_def (z : ℤ) :
    (↑z : AddMonoid.End M) = DistribMulAction.toAddMonoidEnd ℤ M z := rfl

