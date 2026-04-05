import Mathlib

open scoped Ring

variable {R : Type u}

theorem star_sub [AddGroup R] [StarAddMonoid R] (r s : R) : star (r - s) = star r - star s := (starAddEquiv : R ≃+ R).map_sub _ _

