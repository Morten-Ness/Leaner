import Mathlib

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem mem_sup_right {S T : Subalgebra R A} : ∀ {x : A}, x ∈ T → x ∈ S ⊔ T := have : T ≤ S ⊔ T := le_sup_right; (this ·)

