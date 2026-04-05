import Mathlib

open scoped Ring

variable {R : Type u}

theorem star_natCast [NonAssocSemiring R] [StarRing R] (n : ℕ) : star (n : R) = n := (congr_arg unop (map_natCast (starRingEquiv : R ≃+* Rᵐᵒᵖ) n)).trans (unop_natCast _)

