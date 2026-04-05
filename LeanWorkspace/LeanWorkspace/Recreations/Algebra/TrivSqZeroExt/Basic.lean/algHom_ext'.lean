import Mathlib

open scoped RightActions

variable (S : Type*) (R R' : Type u) (M : Type v)

variable [CommSemiring S] [Semiring R] [CommSemiring R'] [AddCommMonoid M]

variable [Algebra S R] [Module S M] [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]

variable [IsScalarTower S R M] [IsScalarTower S Rᵐᵒᵖ M]

variable [Module R' M] [Module R'ᵐᵒᵖ M] [IsCentralScalar R' M]

theorem algHom_ext' {A} [Semiring A] [Algebra S A] ⦃f g : tsze R M →ₐ[S] A⦄
    (hinl : f.comp (TrivSqZeroExt.inlAlgHom S R M) = g.comp (TrivSqZeroExt.inlAlgHom S R M))
    (hinr : f.toLinearMap.comp (TrivSqZeroExt.inrHom R M |>.restrictScalars S) =
      g.toLinearMap.comp (TrivSqZeroExt.inrHom R M |>.restrictScalars S)) : f = g := AlgHom.toLinearMap_injective <|
    TrivSqZeroExt.linearMap_ext (AlgHom.congr_fun hinl) (LinearMap.congr_fun hinr)

