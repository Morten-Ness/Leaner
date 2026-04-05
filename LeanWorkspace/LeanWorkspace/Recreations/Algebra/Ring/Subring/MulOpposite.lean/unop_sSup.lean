import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocRing R]

theorem unop_sSup (S : Set (Subring Rᵐᵒᵖ)) : (sSup S).unop = sSup (.op ⁻¹' S) := Subring.opEquiv.symm.map_sSup_eq_sSup_symm_preimage _

