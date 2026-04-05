import Mathlib

open scoped Ring

variable {R : Type u}

theorem star_zero [AddMonoid R] [StarAddMonoid R] : star (0 : R) = 0 := (starAddEquiv : R ≃+ R).map_zero

