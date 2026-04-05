import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocSemiring R]

theorem unop_eq_top {S : Subsemiring Rᵐᵒᵖ} : S.unop = ⊤ ↔ S = ⊤ := Subsemiring.unop_injective.eq_iff' Subsemiring.unop_top

