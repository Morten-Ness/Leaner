import Mathlib

variable {ι : Sort*} {M : Type*} [Mul M]

theorem op_sInf (S : Set (Subsemigroup M)) : (sInf S).op = sInf (.unop ⁻¹' S) := Subsemigroup.opEquiv.map_sInf_eq_sInf_symm_preimage _

