import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocSemiring R]

theorem unop_sSup (S : Set (Subsemiring Rᵐᵒᵖ)) : (sSup S).unop = sSup (.op ⁻¹' S) := Subsemiring.opEquiv.symm.map_sSup_eq_sSup_symm_preimage _

