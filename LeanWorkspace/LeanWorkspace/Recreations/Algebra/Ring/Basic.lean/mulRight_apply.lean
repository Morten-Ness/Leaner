import Mathlib

variable {R S : Type*}

variable [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] {a b : R}

theorem mulRight_apply (a r : R) : AddMonoidHom.mulRight r a = a * r := rfl

