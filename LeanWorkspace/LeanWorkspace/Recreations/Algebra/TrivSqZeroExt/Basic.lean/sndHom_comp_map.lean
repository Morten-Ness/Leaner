import Mathlib

open scoped RightActions

variable (S : Type*) (R R' : Type u) (M : Type v)

variable [CommSemiring S] [Semiring R] [CommSemiring R'] [AddCommMonoid M]

variable [Algebra S R] [Module S M] [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]

variable [IsScalarTower S R M] [IsScalarTower S Rᵐᵒᵖ M]

variable [Module R' M] [Module R'ᵐᵒᵖ M] [IsCentralScalar R' M]

variable {A : Type*} [Semiring A] [Algebra S A] [Algebra R' A]

variable {N P : Type*} [AddCommMonoid N] [Module R' N] [Module R'ᵐᵒᵖ N] [IsCentralScalar R' N]
  [AddCommMonoid P] [Module R' P] [Module R'ᵐᵒᵖ P] [IsCentralScalar R' P]

theorem sndHom_comp_map (f : M →ₗ[R'] N) :
    TrivSqZeroExt.sndHom R' N ∘ₗ (TrivSqZeroExt.map f).toLinearMap = f ∘ₗ TrivSqZeroExt.sndHom R' M := LinearMap.ext <| TrivSqZeroExt.snd_map _

