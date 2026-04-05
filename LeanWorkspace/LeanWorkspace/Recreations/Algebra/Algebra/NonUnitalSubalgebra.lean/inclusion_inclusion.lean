import Mathlib

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R]

variable [NonUnitalNonAssocSemiring A] [Module R A]

variable (S : NonUnitalSubalgebra R A)

variable [NonUnitalNonAssocSemiring B] [Module R B]

theorem inclusion_inclusion {S T U : NonUnitalSubalgebra R A} (hst : S ≤ T) (htu : T ≤ U) (x : S) :
    NonUnitalSubalgebra.inclusion htu (NonUnitalSubalgebra.inclusion hst x) = NonUnitalSubalgebra.inclusion (le_trans hst htu) x := Subtype.ext rfl

