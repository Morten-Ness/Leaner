import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocRing R]

theorem op_sSup (S : Set (Subring R)) : (sSup S).op = sSup (.unop ⁻¹' S) := Subring.opEquiv.map_sSup_eq_sSup_symm_preimage _

