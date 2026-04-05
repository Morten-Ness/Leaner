import Mathlib

variable {ι : Sort*} {G : Type*} [Group G]

theorem op_sInf (S : Set (Subgroup G)) : (sInf S).op = sInf (.unop ⁻¹' S) := opEquiv.map_sInf_eq_sInf_symm_preimage _

