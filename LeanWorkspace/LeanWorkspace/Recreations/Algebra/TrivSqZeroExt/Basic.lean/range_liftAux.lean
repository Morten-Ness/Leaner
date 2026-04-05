import Mathlib

open scoped RightActions

variable (S : Type*) (R R' : Type u) (M : Type v)

variable [CommSemiring S] [Semiring R] [CommSemiring R'] [AddCommMonoid M]

variable [Algebra S R] [Module S M] [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]

variable [IsScalarTower S R M] [IsScalarTower S Rᵐᵒᵖ M]

variable [Module R' M] [Module R'ᵐᵒᵖ M] [IsCentralScalar R' M]

variable {A : Type*} [Semiring A] [Algebra S A] [Algebra R' A]

theorem range_liftAux (f : R →ₐ[S] A) (g : M →ₗ[S] A)
    (hg : ∀ x y, g x * g y = 0)
    (hfg : ∀ r x, g (r •> x) = f r * g x)
    (hgf : ∀ r x, g (x <• r) = g x * f r) :
    (TrivSqZeroExt.lift f g hg hfg hgf).range = f.range ⊔ Algebra.adjoin S (Set.range g) := by
  simp_rw [← Algebra.map_top, ← TrivSqZeroExt.range_inlAlgHom_sup_adjoin_range_inr, Algebra.map_sup,
    AlgHom.map_adjoin, ← AlgHom.range_comp, TrivSqZeroExt.lift_comp_inlHom, ← Set.range_comp, Function.comp_def,
    TrivSqZeroExt.lift_apply_inr, Algebra.map_top]

