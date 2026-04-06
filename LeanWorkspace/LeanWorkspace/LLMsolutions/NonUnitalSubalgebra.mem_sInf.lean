FAIL
import Mathlib

variable {F : Type*} (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

variable [NonUnitalNonAssocSemiring B] [Module R B]

variable [FunLike F A B] [NonUnitalAlgHomClass F R A B]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem mem_sInf {S : Set (NonUnitalSubalgebra R A)} {x : A} : x ∈ sInf S ↔ ∀ p ∈ S, x ∈ p := by
  constructor
  · intro hx p hp
    exact show x ∈ p from (sInf_le hp) hx
  · intro hx
    rw [show sInf S = sInf {p | p ∈ S} by rfl]
    exact by
      change x ∈ sInf {p : NonUnitalSubalgebra R A | p ∈ S}
      exact hx
