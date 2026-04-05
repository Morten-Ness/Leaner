import Mathlib

open scoped Ring

variable {R : Type u}

variable [Monoid R] [StarMul R]

theorem coe_star (u : Rˣ) : ↑(star u) = (star ↑u : R) := rfl

