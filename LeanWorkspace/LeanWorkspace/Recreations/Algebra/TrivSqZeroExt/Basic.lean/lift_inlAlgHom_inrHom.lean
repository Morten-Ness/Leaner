import Mathlib

open scoped RightActions

variable (S : Type*) (R R' : Type u) (M : Type v)

variable [CommSemiring S] [Semiring R] [CommSemiring R'] [AddCommMonoid M]

variable [Algebra S R] [Module S M] [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]

variable [IsScalarTower S R M] [IsScalarTower S Rᵐᵒᵖ M]

variable [Module R' M] [Module R'ᵐᵒᵖ M] [IsCentralScalar R' M]

variable {A : Type*} [Semiring A] [Algebra S A] [Algebra R' A]

theorem lift_inlAlgHom_inrHom :
    TrivSqZeroExt.lift (TrivSqZeroExt.inlAlgHom _ _ _) (TrivSqZeroExt.inrHom R M |>.restrictScalars S)
      (TrivSqZeroExt.inr_mul_inr R) (fun _ _ => (TrivSqZeroExt.inl_mul_inr _ _).symm) (fun _ _ => (TrivSqZeroExt.inr_mul_inl _ _).symm) =
    AlgHom.id S (tsze R M) := TrivSqZeroExt.algHom_ext' (TrivSqZeroExt.lift_comp_inlHom _ _ _ _ _) (TrivSqZeroExt.lift_comp_inrHom _ _ _ _ _)

