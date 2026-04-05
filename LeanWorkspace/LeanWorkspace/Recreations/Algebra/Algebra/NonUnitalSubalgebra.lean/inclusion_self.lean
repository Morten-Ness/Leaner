import Mathlib

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R]

variable [NonUnitalNonAssocSemiring A] [Module R A]

variable (S : NonUnitalSubalgebra R A)

variable [NonUnitalNonAssocSemiring B] [Module R B]

theorem inclusion_self {S : NonUnitalSubalgebra R A} :
    NonUnitalSubalgebra.inclusion (le_refl S) = NonUnitalAlgHom.id R S := rfl

