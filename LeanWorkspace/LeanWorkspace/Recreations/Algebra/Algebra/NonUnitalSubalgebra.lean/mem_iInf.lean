import Mathlib

variable {F : Type*} (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

variable [NonUnitalNonAssocSemiring B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem mem_iInf {ι : Sort*} {S : ι → NonUnitalSubalgebra R A} {x : A} :
    x ∈ ⨅ i, S i ↔ ∀ i, x ∈ S i := by simp only [iInf, NonUnitalAlgebra.mem_sInf, Set.forall_mem_range]

