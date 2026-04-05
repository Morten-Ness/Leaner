import Mathlib

variable {ι : Sort*} {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem unop_sSup (S : Set (Subalgebra R Aᵐᵒᵖ)) : (sSup S).unop = sSup (.op ⁻¹' S) := Subalgebra.opEquiv.symm.map_sSup_eq_sSup_symm_preimage _

