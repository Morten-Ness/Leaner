import Mathlib

open scoped Ring

variable {R : Type u}

theorem star_eq_zero [AddMonoid R] [StarAddMonoid R] {x : R} : star x = 0 ↔ x = 0 := starAddEquiv.map_eq_zero_iff (M := R)

