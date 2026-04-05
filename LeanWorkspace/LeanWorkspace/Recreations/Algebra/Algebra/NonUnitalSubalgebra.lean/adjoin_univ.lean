import Mathlib

variable {F : Type*} (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

variable [NonUnitalNonAssocSemiring B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem adjoin_univ : NonUnitalAlgebra.adjoin R (Set.univ : Set A) = ⊤ := eq_top_iff.2 fun _x hx => NonUnitalAlgebra.subset_adjoin R hx

