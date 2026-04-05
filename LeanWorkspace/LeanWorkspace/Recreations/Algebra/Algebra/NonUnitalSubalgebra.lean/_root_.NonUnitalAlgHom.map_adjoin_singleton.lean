import Mathlib

variable {F : Type*} (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

variable [NonUnitalNonAssocSemiring B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem _root_.NonUnitalAlgHom.map_adjoin_singleton [IsScalarTower R B B] [SMulCommClass R B B]
    (f : F) (x : A) : NonUnitalSubalgebra.map f (NonUnitalAlgebra.adjoin R {x}) = NonUnitalAlgebra.adjoin R {f x} := by
  simp [NonUnitalAlgHom.map_adjoin]

