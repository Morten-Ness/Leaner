import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocRing R]

theorem unop_sInf (S : Set (Subring Rᵐᵒᵖ)) : (sInf S).unop = sInf (.op ⁻¹' S) := Subring.opEquiv.symm.map_sInf_eq_sInf_symm_preimage _

