import Mathlib

variable {ι : Sort*} {M : Type*} [MulOneClass M]

theorem unop_inj {S T : Submonoid Mᵐᵒᵖ} : S.unop = T.unop ↔ S = T := Submonoid.opEquiv.symm.eq_iff_eq

