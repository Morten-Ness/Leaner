import Mathlib

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

variable [AddCommMonoid M] [Module R M] [Module A M] [Module B M]

variable [IsScalarTower R A M] [IsScalarTower R B M] [SMulCommClass A B M]

theorem lsmul_coe (a : A) : (Algebra.lsmul R B M a : M → M) = (a • ·) := rfl

