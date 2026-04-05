import Mathlib

variable (R : Type u) {A : Type v} {B : Type w}

variable [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

theorem coe_inf (S T : Subalgebra R A) : (↑(S ⊓ T) : Set A) = (S ∩ T : Set A) := rfl

