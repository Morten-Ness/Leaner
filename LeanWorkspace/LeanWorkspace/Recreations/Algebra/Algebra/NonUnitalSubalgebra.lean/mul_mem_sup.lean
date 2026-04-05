import Mathlib

variable {F : Type*} (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

variable [NonUnitalNonAssocSemiring B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem mul_mem_sup {S T : NonUnitalSubalgebra R A} {x y : A} (hx : x ∈ S) (hy : y ∈ T) :
    x * y ∈ S ⊔ T := mul_mem (NonUnitalAlgebra.mem_sup_left hx) (NonUnitalAlgebra.mem_sup_right hy)

