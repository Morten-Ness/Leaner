import Mathlib

variable {R S A B : Type*}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra R B] [Algebra S A] [SMulCommClass R S A]

variable [IsScalarTower R S A]

theorem toRingEquiv_op (f : A ≃ₐ[R] B) :
    (AlgEquiv.op f).toRingEquiv = RingEquiv.op f.toRingEquiv := rfl

