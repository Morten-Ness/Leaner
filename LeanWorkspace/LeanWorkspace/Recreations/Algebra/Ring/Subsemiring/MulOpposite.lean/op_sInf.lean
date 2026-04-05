import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocSemiring R]

theorem op_sInf (S : Set (Subsemiring R)) : (sInf S).op = sInf (.unop ⁻¹' S) := Subsemiring.opEquiv.map_sInf_eq_sInf_symm_preimage _

