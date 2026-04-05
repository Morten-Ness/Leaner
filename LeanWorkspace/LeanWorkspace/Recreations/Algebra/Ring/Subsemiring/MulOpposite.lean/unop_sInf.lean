import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocSemiring R]

theorem unop_sInf (S : Set (Subsemiring Rᵐᵒᵖ)) : (sInf S).unop = sInf (.op ⁻¹' S) := Subsemiring.opEquiv.symm.map_sInf_eq_sInf_symm_preimage _

