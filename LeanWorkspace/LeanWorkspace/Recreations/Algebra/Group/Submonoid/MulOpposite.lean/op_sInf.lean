import Mathlib

variable {ι : Sort*} {M : Type*} [MulOneClass M]

theorem op_sInf (S : Set (Submonoid M)) : (sInf S).op = sInf (.unop ⁻¹' S) := Submonoid.opEquiv.map_sInf_eq_sInf_symm_preimage _

