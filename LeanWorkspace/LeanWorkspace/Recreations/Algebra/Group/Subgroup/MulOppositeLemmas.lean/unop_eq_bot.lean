import Mathlib

variable {ι : Sort*} {G : Type*} [Group G]

theorem unop_eq_bot {S : Subgroup Gᵐᵒᵖ} : S.unop = ⊥ ↔ S = ⊥ := unop_injective.eq_iff' Subgroup.unop_bot

