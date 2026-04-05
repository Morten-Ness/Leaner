import Mathlib

variable {ι : Sort*} {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem op_sInf (S : Set (Subalgebra R A)) : (sInf S).op = sInf (.unop ⁻¹' S) := Subalgebra.opEquiv.map_sInf_eq_sInf_symm_preimage _

