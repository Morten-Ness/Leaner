import Mathlib

variable {R : Type*} {R₂ : Type*} {R₃ : Type*}

variable {K : Type*}

variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable {V : Type*} {V₂ : Type*}

variable (R : Type*) {S M N : Type*} [Semiring R] [Semiring S] [SMul R S]

variable [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]

variable [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]

theorem ker_restrictScalars (f : M →ₗ[S] N) :
    LinearMap.ker (f.restrictScalars R) = (LinearMap.ker f).restrictScalars R := rfl

