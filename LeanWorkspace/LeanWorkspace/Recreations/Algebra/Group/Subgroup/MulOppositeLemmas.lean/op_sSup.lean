import Mathlib

variable {ι : Sort*} {G : Type*} [Group G]

theorem op_sSup (S : Set (Subgroup G)) : (sSup S).op = sSup (.unop ⁻¹' S) := opEquiv.map_sSup_eq_sSup_symm_preimage _

