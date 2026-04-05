import Mathlib

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiring R]

variable [NonUnitalNonAssocSemiring A] [Module R A]

variable (S : NonUnitalSubalgebra R A)

variable [NonUnitalNonAssocSemiring B] [Module R B]

variable (S₁ : NonUnitalSubalgebra R B)

theorem coe_prod : (NonUnitalSubalgebra.prod S S₁ : Set (A × B)) = (S : Set A) ×ˢ S₁ := rfl

