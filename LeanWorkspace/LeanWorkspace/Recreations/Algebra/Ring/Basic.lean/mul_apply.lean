import Mathlib

variable {R S : Type*}

variable [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] {a b : R}

theorem mul_apply (x y : R) : AddMonoidHom.mul x y = x * y := rfl

