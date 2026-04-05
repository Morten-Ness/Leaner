import Mathlib

variable {ι : Sort*} {G : Type*} [Group G]

theorem unop_inj {S T : Subgroup Gᵐᵒᵖ} : S.unop = T.unop ↔ S = T := Subgroup.opEquiv.symm.eq_iff_eq

