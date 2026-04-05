import Mathlib

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R]

variable [NonUnitalNonAssocSemiring A] [Module R A]

variable (S : NonUnitalSubalgebra R A)

variable [NonUnitalNonAssocSemiring B] [Module R B]

theorem inclusion_right {S T : NonUnitalSubalgebra R A} (h : S ≤ T) (x : T) (m : (x : A) ∈ S) :
    NonUnitalSubalgebra.inclusion h ⟨x, m⟩ = x := Subtype.ext rfl

