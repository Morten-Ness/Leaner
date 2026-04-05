import Mathlib

open scoped RightActions

variable (S : Type*) (R R' : Type u) (M : Type v)

variable [CommSemiring S] [Semiring R] [CommSemiring R'] [AddCommMonoid M]

variable [Algebra S R] [Module S M] [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]

variable [IsScalarTower S R M] [IsScalarTower S Rᵐᵒᵖ M]

variable [Module R' M] [Module R'ᵐᵒᵖ M] [IsCentralScalar R' M]

variable {A : Type*} [Semiring A] [Algebra S A] [Algebra R' A]

theorem lift_comp_inlHom (f : R →ₐ[S] A) (g : M →ₗ[S] A)
    (hg : ∀ x y, g x * g y = 0)
    (hfg : ∀ r x, g (r •> x) = f r * g x)
    (hgf : ∀ r x, g (x <• r) = g x * f r) :
    (TrivSqZeroExt.lift f g hg hfg hgf).comp (TrivSqZeroExt.inlAlgHom S R M) = f := AlgHom.ext <| TrivSqZeroExt.lift_apply_inl f g hg hfg hgf

