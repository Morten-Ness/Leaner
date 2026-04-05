import Mathlib

variable {ι : Sort*} {M : Type*} [Mul M]

theorem unop_sInf (S : Set (Subsemigroup Mᵐᵒᵖ)) : (sInf S).unop = sInf (.op ⁻¹' S) := Subsemigroup.opEquiv.symm.map_sInf_eq_sInf_symm_preimage _

