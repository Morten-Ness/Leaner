FAIL
import Mathlib

variable {F : Type*} (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

variable [NonUnitalNonAssocSemiring B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem mem_iInf {ι : Sort*} {S : ι → NonUnitalSubalgebra R A} {x : A} :
    x ∈ ⨅ i, S i ↔ ∀ i, x ∈ S i := by
  constructor
  · intro hx i
    exact show x ∈ S i from (show (⨅ i, S i) ≤ S i from iInf_le S i) hx
  · intro hx
    refine mem_iInf.2 ?_
    intro i
    exact hx i
