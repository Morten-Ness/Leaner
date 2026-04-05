import Mathlib

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

theorem starClosure_toSubalgebra (S : Subalgebra R A) :
    S.starClosure.toSubalgebra = S ⊔ star S := rfl

