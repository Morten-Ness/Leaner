import Mathlib

variable {ι : Sort*} {M : Type*} [MulOneClass M]

theorem unop_sInf (S : Set (Submonoid Mᵐᵒᵖ)) : (sInf S).unop = sInf (.op ⁻¹' S) := Submonoid.opEquiv.symm.map_sInf_eq_sInf_symm_preimage _

