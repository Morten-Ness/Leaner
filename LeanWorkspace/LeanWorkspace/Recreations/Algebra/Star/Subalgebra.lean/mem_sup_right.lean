import Mathlib

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

theorem mem_sup_right {S T : StarSubalgebra R A} : ∀ {x : A}, x ∈ T → x ∈ S ⊔ T := have : T ≤ S ⊔ T := le_sup_right; (this ·)

