import Mathlib

open scoped Ring

variable {R : Type u}

variable [Monoid R] [StarMul R]

theorem coe_star_inv (u : Rˣ) : ↑(star u)⁻¹ = (star ↑u⁻¹ : R) := rfl

