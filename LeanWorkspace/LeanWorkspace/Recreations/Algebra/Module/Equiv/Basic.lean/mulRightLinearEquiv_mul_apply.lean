import Mathlib

variable {R : Type*} {R₂ : Type*}

variable {K : Type*} {S : Type*} {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable {R A : Type*} [Semiring R] [Semiring A] [Module R A]

variable [IsScalarTower R A A]

theorem mulRightLinearEquiv_mul_apply (u v : Aˣ) (x : A) :
    Units.mulRightLinearEquiv R (u * v) x =
      Units.mulRightLinearEquiv R v (Units.mulRightLinearEquiv R u x) := by simp [mul_assoc]

