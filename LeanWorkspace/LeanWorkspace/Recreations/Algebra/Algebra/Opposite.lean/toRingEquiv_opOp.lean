import Mathlib

variable {R S A B : Type*}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra R B] [Algebra S A] [SMulCommClass R S A]

variable [IsScalarTower R S A]

theorem toRingEquiv_opOp : (AlgEquiv.opOp R A : A ≃+* Aᵐᵒᵖᵐᵒᵖ) = RingEquiv.opOp A := rfl

