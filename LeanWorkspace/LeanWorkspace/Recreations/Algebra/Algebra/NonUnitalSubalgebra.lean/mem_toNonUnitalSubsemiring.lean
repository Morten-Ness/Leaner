import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u} {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R]

variable [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B] [NonUnitalNonAssocSemiring C]

variable [Module R A] [Module R B] [Module R C]

theorem mem_toNonUnitalSubsemiring {S : NonUnitalSubalgebra R A} {x} :
    x ∈ S.toNonUnitalSubsemiring ↔ x ∈ S := Iff.rfl

