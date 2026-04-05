import Mathlib

open scoped Ring

variable {R : Type u}

theorem star_inj [InvolutiveStar R] {x y : R} : star x = star y ↔ x = y := star_injective.eq_iff

