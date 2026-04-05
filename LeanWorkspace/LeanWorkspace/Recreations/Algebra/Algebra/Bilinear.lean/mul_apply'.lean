import Mathlib

variable {R A B : Type*}

variable (R A) [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]

variable [SMulCommClass R A A] [IsScalarTower R A A]

theorem mul_apply' (a b : A) : LinearMap.mul R A a b = a * b := rfl

