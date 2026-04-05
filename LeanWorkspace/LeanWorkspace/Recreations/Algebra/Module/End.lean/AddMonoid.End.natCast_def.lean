import Mathlib

variable {R S M M₂ : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] (r s : R) (x : M)

theorem AddMonoid.End.natCast_def (n : ℕ) :
    (↑n : AddMonoid.End M) = DistribMulAction.toAddMonoidEnd ℕ M n := rfl

