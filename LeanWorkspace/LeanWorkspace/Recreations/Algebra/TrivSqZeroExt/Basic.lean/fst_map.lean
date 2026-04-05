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

theorem fst_map (f : M →ₗ[R'] N) (x : TrivSqZeroExt R' M) : TrivSqZeroExt.fst (TrivSqZeroExt.map f x) = TrivSqZeroExt.fst x := by
  simp [TrivSqZeroExt.map, TrivSqZeroExt.lift_def, Algebra.ofId_apply, TrivSqZeroExt.algebraMap_eq_inl]

