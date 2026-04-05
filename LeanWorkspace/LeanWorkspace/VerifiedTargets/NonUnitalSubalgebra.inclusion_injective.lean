import Mathlib

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R]

variable [NonUnitalNonAssocSemiring A] [Module R A]

variable (S : NonUnitalSubalgebra R A)

variable [NonUnitalNonAssocSemiring B] [Module R B]

theorem inclusion_injective {S T : NonUnitalSubalgebra R A} (h : S ≤ T) :
    Function.Injective (NonUnitalSubalgebra.inclusion h) := fun _ _ => Subtype.ext ∘ Subtype.mk.inj

