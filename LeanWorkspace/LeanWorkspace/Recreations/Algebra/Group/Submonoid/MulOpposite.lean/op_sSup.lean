import Mathlib

variable {ι : Sort*} {M : Type*} [MulOneClass M]

theorem op_sSup (S : Set (Submonoid M)) : (sSup S).op = sSup (.unop ⁻¹' S) := Submonoid.opEquiv.map_sSup_eq_sSup_symm_preimage _

