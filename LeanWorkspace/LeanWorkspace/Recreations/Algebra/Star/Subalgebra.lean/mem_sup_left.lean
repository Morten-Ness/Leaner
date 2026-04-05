import Mathlib

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

theorem mem_sup_left {S T : StarSubalgebra R A} : ∀ {x : A}, x ∈ S → x ∈ S ⊔ T := have : S ≤ S ⊔ T := le_sup_left; (this ·)

