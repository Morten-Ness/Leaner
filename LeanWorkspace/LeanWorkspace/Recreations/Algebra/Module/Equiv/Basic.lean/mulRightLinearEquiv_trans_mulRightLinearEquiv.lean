import Mathlib

variable {R : Type*} {R₂ : Type*}

variable {K : Type*} {S : Type*} {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

variable {R A : Type*} [Semiring R] [Semiring A] [Module R A]

variable [IsScalarTower R A A]

theorem mulRightLinearEquiv_trans_mulRightLinearEquiv (a b : Aˣ) :
    (a.mulRightLinearEquiv R).trans (b.mulRightLinearEquiv R) =
      (a * b).mulRightLinearEquiv R := by ext; simp [mul_assoc]

