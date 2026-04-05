import Mathlib

variable {F R A B : Type*} [CommSemiring R] [StarRing R]

variable [Semiring A] [Algebra R A] [StarRing A] [StarModule R A]

variable [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

theorem mem_starClosure (S : Subalgebra R A) {x : A} :
    x ∈ S.starClosure ↔ x ∈ S ⊔ star S := Iff.rfl

