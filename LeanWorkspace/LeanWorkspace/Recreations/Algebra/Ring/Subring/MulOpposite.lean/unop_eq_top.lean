import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocRing R]

theorem unop_eq_top {S : Subring Rᵐᵒᵖ} : S.unop = ⊤ ↔ S = ⊤ := Subring.unop_injective.eq_iff' Subring.unop_top

