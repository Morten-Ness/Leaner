import Mathlib

variable {R S A B : Type*}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra R B] [Algebra S A] [SMulCommClass R S A]

variable [IsScalarTower R S A]

theorem toRingEquiv_unop (f : Aᵐᵒᵖ ≃ₐ[R] Bᵐᵒᵖ) :
    (AlgEquiv.unop f).toRingEquiv = RingEquiv.unop f.toRingEquiv := rfl

