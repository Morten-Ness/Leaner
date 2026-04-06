import Mathlib

variable {F : Type*} (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

variable [NonUnitalNonAssocSemiring B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem mem_sup_right {S T : NonUnitalSubalgebra R A} : ∀ {x : A}, x ∈ T → x ∈ S ⊔ T :=
by
  intro x hx
  exact (show T ≤ S ⊔ T from le_sup_right) hx
