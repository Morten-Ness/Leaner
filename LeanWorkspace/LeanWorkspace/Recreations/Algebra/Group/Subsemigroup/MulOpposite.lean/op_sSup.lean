import Mathlib

variable {ι : Sort*} {M : Type*} [Mul M]

theorem op_sSup (S : Set (Subsemigroup M)) : (sSup S).op = sSup (.unop ⁻¹' S) := Subsemigroup.opEquiv.map_sSup_eq_sSup_symm_preimage _

