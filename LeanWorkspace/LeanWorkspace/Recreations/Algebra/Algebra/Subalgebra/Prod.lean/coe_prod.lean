import Mathlib

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

variable (S : Subalgebra R A) (S₁ : Subalgebra R B)

theorem coe_prod : (Subalgebra.prod S S₁ : Set (A × B)) = (S : Set A) ×ˢ (S₁ : Set B) := rfl

