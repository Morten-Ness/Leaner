import Mathlib

open scoped Pointwise

variable {F : Type v'} {R' : Type u'} {R : Type u}

variable {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R] [StarRing R]

variable [NonUnitalSemiring A] [StarRing A] [Module R A]

variable [StarModule R A]

variable [IsScalarTower R A A] [SMulCommClass R A A]

theorem mem_starClosure (S : NonUnitalSubalgebra R A) {x : A} :
    x ∈ S.starClosure ↔ x ∈ S ⊔ star S := Iff.rfl

