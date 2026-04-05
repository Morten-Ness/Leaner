import Mathlib

variable (R : Type u) (S : Type v) (A : Type w) (B : Type u₁) (M : Type v₁)

variable [CommSemiring R] [Semiring A] [IsDomain A] [Semiring B] [Algebra R A] [Algebra R B]

variable [AddCommGroup M] [Module R M] [Module A M] [Module B M]

variable [IsScalarTower R A M] [IsScalarTower R B M] [SMulCommClass A B M]

theorem lsmul_injective [Module.IsTorsionFree A M] {x : A} (hx : x ≠ 0) :
    Function.Injective (Algebra.lsmul R B M x) := smul_right_injective M hx

