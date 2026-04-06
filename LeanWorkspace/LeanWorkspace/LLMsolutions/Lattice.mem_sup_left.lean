import Mathlib

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem mem_sup_left {S T : Subalgebra R A} : ∀ {x : A}, x ∈ S → x ∈ S ⊔ T :=
  fun {x} hx => by
    exact show x ∈ S ⊔ T from SetLike.mem_of_subset (show S ≤ S ⊔ T from le_sup_left) hx
