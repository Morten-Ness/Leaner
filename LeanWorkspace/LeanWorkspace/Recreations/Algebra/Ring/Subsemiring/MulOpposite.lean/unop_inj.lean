import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocSemiring R]

theorem unop_inj {S T : Subsemiring Rᵐᵒᵖ} : S.unop = T.unop ↔ S = T := Subsemiring.opEquiv.symm.eq_iff_eq

