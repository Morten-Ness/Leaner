import Mathlib

variable {R : Type*} {R₂ : Type*}

variable {K : Type*} {S : Type*} {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

theorem LinearEquiv.smul_refl [Semiring R] [Semiring S] [AddCommMonoid M] [Module R M] [Module S M]
    [SMulCommClass R S M] [SMul S R] [IsScalarTower S R M] (α : Sˣ) :
    letI := SMulCommClass.symm R Sˣ M
    α • refl R M = DistribMulAction.toLinearEquiv R M α := rfl

