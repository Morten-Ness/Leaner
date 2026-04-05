import Mathlib

variable {F : Type*} (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

variable [NonUnitalNonAssocSemiring B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem mem_bot {x : A} : x ∈ (⊥ : NonUnitalSubalgebra R A) ↔ x = 0 := show x ∈ Submodule.span R (NonUnitalSubsemiring.closure (∅ : Set A) : Set A) ↔ x = 0 by
    rw [NonUnitalSubsemiring.closure_empty, NonUnitalSubsemiring.coe_bot,
      Submodule.span_zero_singleton, Submodule.mem_bot]

