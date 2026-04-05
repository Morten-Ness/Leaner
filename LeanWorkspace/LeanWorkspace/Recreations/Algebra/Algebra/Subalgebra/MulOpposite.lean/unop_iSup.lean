import Mathlib

variable {ι : Sort*} {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem unop_iSup (S : ι → Subalgebra R Aᵐᵒᵖ) : (iSup S).unop = ⨆ i, (S i).unop := Subalgebra.opEquiv.symm.map_iSup _

