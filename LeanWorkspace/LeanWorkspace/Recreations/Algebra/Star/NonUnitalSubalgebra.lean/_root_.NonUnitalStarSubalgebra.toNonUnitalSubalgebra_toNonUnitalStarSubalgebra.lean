import Mathlib

variable {F : Type v'} {R' : Type u'} {R : Type u}

variable {A : Type v} {B : Type w} {C : Type w'}

variable [CommSemiring R] [NonUnitalSemiring A] [Module R A] [Star A]

variable (s : NonUnitalSubalgebra R A)

theorem _root_.NonUnitalStarSubalgebra.toNonUnitalSubalgebra_toNonUnitalStarSubalgebra
    (S : NonUnitalStarSubalgebra R A) :
    (S.toNonUnitalSubalgebra.toNonUnitalStarSubalgebra fun _ => star_mem (s := S)) = S :=
  SetLike.coe_injective rfl

