import Mathlib

variable {ι : Sort*} {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem unop_iInf (S : ι → Subalgebra R Aᵐᵒᵖ) : (iInf S).unop = ⨅ i, (S i).unop := Subalgebra.opEquiv.symm.map_iInf _

