import Mathlib

variable {R S A B : Type*}

variable (R A) [CommSemiring R] [CommSemiring A] [Algebra R A]

theorem toRingEquiv_toOpposite : (AlgEquiv.toOpposite R A : A ≃+* Aᵐᵒᵖ) = RingEquiv.toOpposite A := rfl

