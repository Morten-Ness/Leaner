import Mathlib

variable {R R₁ R₂ R₃ S S₃ T M M₁ M₂ M₃ N₂ N₃ : Type*}

variable {R A : Type*} [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]

variable (R) [IsScalarTower R A A]

theorem mulRight_zero_eq_zero : LinearMap.mulRight R (0 : A) = 0 := LinearMap.ext mul_zero

