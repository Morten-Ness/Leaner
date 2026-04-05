import Mathlib

variable {ι : Sort*} {M : Type*} [Mul M]

theorem unop_sSup (S : Set (Subsemigroup Mᵐᵒᵖ)) : (sSup S).unop = sSup (.op ⁻¹' S) := Subsemigroup.opEquiv.symm.map_sSup_eq_sSup_symm_preimage _

