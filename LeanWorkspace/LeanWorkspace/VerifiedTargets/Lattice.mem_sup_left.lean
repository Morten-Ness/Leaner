import Mathlib

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem mem_sup_left {S T : Subalgebra R A} : ∀ {x : A}, x ∈ S → x ∈ S ⊔ T := have : S ≤ S ⊔ T := le_sup_left; (this ·)

