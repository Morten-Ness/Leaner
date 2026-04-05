import Mathlib

variable {R R₁ R₂ R₃ S S₃ T M M₁ M₂ M₃ N₂ N₃ : Type*}

variable {R A : Type*} [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]

variable [SMulCommClass R A A] [IsScalarTower R A A]

theorem mulLeftRight_apply (a b x : A) : LinearMap.mulLeftRight R (a, b) x = a * x * b := rfl

