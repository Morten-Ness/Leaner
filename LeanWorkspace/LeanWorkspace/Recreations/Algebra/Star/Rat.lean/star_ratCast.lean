import Mathlib

variable {R : Type*}

theorem star_ratCast [DivisionRing R] [StarRing R] (r : ℚ) : star (r : R) = r := (congr_arg unop <| map_ratCast (starRingEquiv : R ≃+* Rᵐᵒᵖ) r).trans (unop_ratCast _)

