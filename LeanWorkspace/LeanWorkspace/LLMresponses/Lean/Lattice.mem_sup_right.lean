import Mathlib

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem mem_sup_right {S T : Subalgebra R A} : ∀ {x : A}, x ∈ T → x ∈ S ⊔ T :=
by
  intro x hx
  exact show x ∈ (S ⊔ T : Subalgebra R A) from (show T ≤ S ⊔ T from le_sup_right) hx
