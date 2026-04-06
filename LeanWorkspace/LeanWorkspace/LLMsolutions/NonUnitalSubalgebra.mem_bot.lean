FAIL
import Mathlib

variable {F : Type*} (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

variable [NonUnitalNonAssocSemiring B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem mem_bot {x : A} : x ∈ (⊥ : NonUnitalSubalgebra R A) ↔ x = 0 := by
  constructor
  · intro hx
    change x ∈ ((⊥ : NonUnitalSubalgebra R A) : Submodule R A) at hx
    simpa using hx
  · intro hx
    rw [hx]
    exact (⊥ : NonUnitalSubalgebra R A).zero_mem
