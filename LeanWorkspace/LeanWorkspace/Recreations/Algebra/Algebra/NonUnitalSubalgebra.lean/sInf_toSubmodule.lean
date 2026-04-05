import Mathlib

variable {F : Type*} (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

variable [NonUnitalNonAssocSemiring B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem sInf_toSubmodule (S : Set (NonUnitalSubalgebra R A)) :
    (sInf S).toSubmodule = sInf (NonUnitalSubalgebra.toSubmodule '' S) := SetLike.coe_injective <| by simp

