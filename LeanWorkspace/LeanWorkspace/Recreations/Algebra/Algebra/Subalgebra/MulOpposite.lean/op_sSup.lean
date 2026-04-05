import Mathlib

variable {ι : Sort*} {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem op_sSup (S : Set (Subalgebra R A)) : (sSup S).op = sSup (.unop ⁻¹' S) := Subalgebra.opEquiv.map_sSup_eq_sSup_symm_preimage _

