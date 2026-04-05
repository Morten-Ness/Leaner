import Mathlib

variable {ι : Sort*} {G : Type*} [Group G]

theorem unop_sSup (S : Set (Subgroup Gᵐᵒᵖ)) : (sSup S).unop = sSup (.op ⁻¹' S) := opEquiv.symm.map_sSup_eq_sSup_symm_preimage _

