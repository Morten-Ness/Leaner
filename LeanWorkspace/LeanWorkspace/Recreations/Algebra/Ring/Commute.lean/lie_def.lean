import Mathlib

variable {R : Type u}

variable [NonUnitalNonAssocRing R]

theorem lie_def (x y : R) : ⁅x, y⁆ = x * y - y * x := rfl

