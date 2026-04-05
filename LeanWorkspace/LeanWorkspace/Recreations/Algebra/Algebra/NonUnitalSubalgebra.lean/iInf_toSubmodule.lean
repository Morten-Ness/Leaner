import Mathlib

variable {F : Type*} (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

variable [NonUnitalNonAssocSemiring B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem iInf_toSubmodule {ι : Sort*} (S : ι → NonUnitalSubalgebra R A) :
    (⨅ i, S i).toSubmodule = ⨅ i, (S i).toSubmodule := SetLike.coe_injective <| by simp

