import Mathlib

variable {ι : Sort*} {M : Type*} [Mul M]

theorem unop_inj {S T : Subsemigroup Mᵐᵒᵖ} : S.unop = T.unop ↔ S = T := Subsemigroup.opEquiv.symm.eq_iff_eq

