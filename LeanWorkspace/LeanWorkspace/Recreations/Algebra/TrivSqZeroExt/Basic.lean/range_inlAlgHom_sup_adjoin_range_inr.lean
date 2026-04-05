import Mathlib

open scoped RightActions

variable (S : Type*) (R R' : Type u) (M : Type v)

variable [CommSemiring S] [Semiring R] [CommSemiring R'] [AddCommMonoid M]

variable [Algebra S R] [Module S M] [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]

variable [IsScalarTower S R M] [IsScalarTower S Rᵐᵒᵖ M]

variable [Module R' M] [Module R'ᵐᵒᵖ M] [IsCentralScalar R' M]

variable {A : Type*} [Semiring A] [Algebra S A] [Algebra R' A]

theorem range_inlAlgHom_sup_adjoin_range_inr :
    (TrivSqZeroExt.inlAlgHom S R M).range ⊔ Algebra.adjoin S (Set.range TrivSqZeroExt.inr) = (⊤ : Subalgebra S (tsze R M)) := by
  refine top_unique fun x hx => ?_; clear hx
  rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq x]
  refine add_mem ?_ ?_
  · exact le_sup_left (α := Subalgebra S _) <| Set.mem_range_self x.fst
  · exact le_sup_right (α := Subalgebra S _) <| Algebra.subset_adjoin <| Set.mem_range_self x.snd

