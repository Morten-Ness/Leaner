import Mathlib

open scoped Ring

variable {R : Type u}

theorem star_ofNat [NonAssocSemiring R] [StarRing R] (n : ℕ) [n.AtLeastTwo] :
    star (ofNat(n) : R) = ofNat(n) := star_natCast _

