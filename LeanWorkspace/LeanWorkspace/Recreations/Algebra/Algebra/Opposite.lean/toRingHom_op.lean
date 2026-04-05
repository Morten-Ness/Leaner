import Mathlib

variable {R S A B : Type*}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra R B] [Algebra S A] [SMulCommClass R S A]

variable [IsScalarTower R S A]

theorem toRingHom_op (f : A →ₐ[R] B) : f.op.toRingHom = RingHom.op f.toRingHom := rfl

