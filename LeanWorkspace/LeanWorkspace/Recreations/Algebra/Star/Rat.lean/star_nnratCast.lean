import Mathlib

variable {R : Type*}

theorem star_nnratCast [DivisionSemiring R] [StarRing R] (q : ℚ≥0) : star (q : R) = q := (congr_arg unop <| map_nnratCast (starRingEquiv : R ≃+* Rᵐᵒᵖ) q).trans (unop_nnratCast _)

