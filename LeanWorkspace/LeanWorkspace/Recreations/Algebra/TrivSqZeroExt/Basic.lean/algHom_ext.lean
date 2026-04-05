import Mathlib

open scoped RightActions

variable (S : Type*) (R R' : Type u) (M : Type v)

variable [CommSemiring S] [Semiring R] [CommSemiring R'] [AddCommMonoid M]

variable [Algebra S R] [Module S M] [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]

variable [IsScalarTower S R M] [IsScalarTower S Rᵐᵒᵖ M]

variable [Module R' M] [Module R'ᵐᵒᵖ M] [IsCentralScalar R' M]

theorem algHom_ext {A} [Semiring A] [Algebra R' A] ⦃f g : tsze R' M →ₐ[R'] A⦄
    (h : ∀ m, f (TrivSqZeroExt.inr m) = g (TrivSqZeroExt.inr m)) : f = g := AlgHom.toLinearMap_injective <|
    TrivSqZeroExt.linearMap_ext (fun _r => (f.commutes _).trans (g.commutes _).symm) h

