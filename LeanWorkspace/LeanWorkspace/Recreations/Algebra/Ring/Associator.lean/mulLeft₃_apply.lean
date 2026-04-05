import Mathlib

variable {R : Type*}

variable [NonUnitalNonAssocSemiring R]

theorem mulLeft₃_apply (x y z : R) : AddMonoidHom.mulLeft₃ x y z = (x * y) * z := rfl

