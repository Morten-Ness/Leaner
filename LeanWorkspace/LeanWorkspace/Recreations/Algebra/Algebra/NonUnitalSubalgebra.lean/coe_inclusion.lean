import Mathlib

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R]

variable [NonUnitalNonAssocSemiring A] [Module R A]

variable (S : NonUnitalSubalgebra R A)

variable [NonUnitalNonAssocSemiring B] [Module R B]

theorem coe_inclusion {S T : NonUnitalSubalgebra R A} (h : S ≤ T) (s : S) :
    (NonUnitalSubalgebra.inclusion h s : A) = s := rfl

