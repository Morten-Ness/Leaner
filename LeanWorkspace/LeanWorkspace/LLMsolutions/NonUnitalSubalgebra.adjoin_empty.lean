import Mathlib

variable {F : Type*} (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

variable [NonUnitalNonAssocSemiring B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem adjoin_empty : NonUnitalAlgebra.adjoin R (∅ : Set A) = ⊥ := by
  apply le_antisymm
  · exact NonUnitalAlgebra.adjoin_le fun x hx => False.elim hx
  · exact bot_le
