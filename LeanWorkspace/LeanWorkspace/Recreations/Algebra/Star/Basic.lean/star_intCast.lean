import Mathlib

open scoped Ring

variable {R : Type u}

theorem star_intCast [NonAssocRing R] [StarRing R] (z : ℤ) : star (z : R) = z := (congr_arg unop <| map_intCast (starRingEquiv : R ≃+* Rᵐᵒᵖ) z).trans (unop_intCast _)

