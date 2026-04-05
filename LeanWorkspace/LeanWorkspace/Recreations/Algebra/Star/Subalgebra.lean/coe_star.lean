import Mathlib

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

theorem coe_star (S : Subalgebra R A) : ((star S : Subalgebra R A) : Set A) = star (S : Set A) := rfl

