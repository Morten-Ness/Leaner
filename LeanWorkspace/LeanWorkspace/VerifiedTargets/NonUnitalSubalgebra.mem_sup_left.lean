import Mathlib

variable {F : Type*} (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

variable [NonUnitalNonAssocSemiring B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem mem_sup_left {S T : NonUnitalSubalgebra R A} : ∀ {x : A}, x ∈ S → x ∈ S ⊔ T := by
  rw [← SetLike.le_def]
  exact le_sup_left

