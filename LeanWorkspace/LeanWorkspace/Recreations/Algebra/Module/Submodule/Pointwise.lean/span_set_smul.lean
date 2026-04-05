import Mathlib

variable {α : Type*} {R : Type*} {M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable {S : Type*} [Monoid S]

variable [DistribMulAction S M]

variable (sR : Set R) (s : Set S) (N : Submodule R M)

theorem span_set_smul [SMulCommClass S R M] (s : Set S) (t : Set M) :
    span R (s • t) = s • span R t := (Submodule.set_smul_span s t).symm

