import Mathlib

variable {ι : Sort*} {G : Type*} [Group G]

theorem unop_sInf (S : Set (Subgroup Gᵐᵒᵖ)) : (sInf S).unop = sInf (.op ⁻¹' S) := opEquiv.symm.map_sInf_eq_sInf_symm_preimage _

