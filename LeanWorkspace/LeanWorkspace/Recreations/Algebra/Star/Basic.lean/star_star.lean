import Mathlib

open scoped Ring

variable {R : Type u}

theorem star_star [InvolutiveStar R] (r : R) : star (star r) = r := star_involutive _

