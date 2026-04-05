import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocRing R]

theorem op_sInf (S : Set (Subring R)) : (sInf S).op = sInf (.unop ⁻¹' S) := Subring.opEquiv.map_sInf_eq_sInf_symm_preimage _

