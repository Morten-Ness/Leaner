import Mathlib

variable {R : Type*}

variable [NonUnitalNonAssocSemiring R]

theorem mulRight₃_apply (x y z : R) : AddMonoidHom.mulRight₃ x y z = x * (y * z) := rfl

