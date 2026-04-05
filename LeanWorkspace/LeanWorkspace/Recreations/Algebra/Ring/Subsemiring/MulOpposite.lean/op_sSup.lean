import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocSemiring R]

theorem op_sSup (S : Set (Subsemiring R)) : (sSup S).op = sSup (.unop ⁻¹' S) := Subsemiring.opEquiv.map_sSup_eq_sSup_symm_preimage _

