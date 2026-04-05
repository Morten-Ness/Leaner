import Mathlib

variable {ι : Sort*} {M : Type*} [MulOneClass M]

theorem unop_sSup (S : Set (Submonoid Mᵐᵒᵖ)) : (sSup S).unop = sSup (.op ⁻¹' S) := Submonoid.opEquiv.symm.map_sSup_eq_sSup_symm_preimage _

