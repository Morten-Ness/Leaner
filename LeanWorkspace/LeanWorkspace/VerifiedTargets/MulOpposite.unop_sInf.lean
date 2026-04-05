import Mathlib

variable {ι : Sort*} {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem unop_sInf (S : Set (Subalgebra R Aᵐᵒᵖ)) : (sInf S).unop = sInf (.op ⁻¹' S) := Subalgebra.opEquiv.symm.map_sInf_eq_sInf_symm_preimage _

