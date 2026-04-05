import Mathlib

variable {R : Type*}

variable [NonUnitalNonAssocRing R]

theorem associator_apply (x y z : R) : associator x y z = (x * y) * z - x * (y * z) := rfl

