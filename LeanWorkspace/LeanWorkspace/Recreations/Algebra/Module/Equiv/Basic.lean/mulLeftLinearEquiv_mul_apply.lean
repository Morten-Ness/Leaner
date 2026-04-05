import Mathlib

variable {R : Type*} {R₂ : Type*}

variable {K : Type*} {S : Type*} {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable {R A : Type*} [Semiring R] [Semiring A] [Module R A]

variable [SMulCommClass R A A]

theorem mulLeftLinearEquiv_mul_apply (u v : Aˣ) (x : A) :
    Units.mulLeftLinearEquiv R A (u * v) x =
      Units.mulLeftLinearEquiv R A u (Units.mulLeftLinearEquiv R A v x) := by simp

