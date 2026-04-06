import Mathlib

variable {F : Type*} (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

variable [NonUnitalNonAssocSemiring B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem mem_adjoin_of_mem {s : Set A} {x : A} (hx : x ∈ s) : x ∈ NonUnitalAlgebra.adjoin R s := by
  exact NonUnitalAlgebra.subset_adjoin (R := R) hx
