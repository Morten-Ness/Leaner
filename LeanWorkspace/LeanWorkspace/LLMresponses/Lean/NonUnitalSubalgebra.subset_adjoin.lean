import Mathlib

variable {F : Type*} (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

variable [NonUnitalNonAssocSemiring B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem subset_adjoin {s : Set A} : s ⊆ NonUnitalAlgebra.adjoin R s := by
  intro x hx
  exact NonUnitalAlgebra.subset_adjoin (R := R) hx
