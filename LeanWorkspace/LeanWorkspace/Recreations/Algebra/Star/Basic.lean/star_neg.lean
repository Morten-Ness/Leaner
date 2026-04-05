import Mathlib

open scoped Ring

variable {R : Type u}

theorem star_neg [AddGroup R] [StarAddMonoid R] (r : R) : star (-r) = -star r := (starAddEquiv : R ≃+ R).map_neg _

