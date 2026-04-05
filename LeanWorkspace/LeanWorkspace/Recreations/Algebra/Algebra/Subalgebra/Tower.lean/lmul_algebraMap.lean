import Mathlib

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

variable [CommSemiring R] [Semiring A] [Algebra R A]

variable [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M]

theorem lmul_algebraMap (x : R) : Algebra.lmul R A (algebraMap R A x) = Algebra.lsmul R R A x := Eq.symm <| LinearMap.ext <| smul_def x

