import Mathlib

variable {ι : Sort*} {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem op_iInf (S : ι → Subalgebra R A) : (iInf S).op = ⨅ i, (S i).op := Subalgebra.opEquiv.map_iInf _

