import Mathlib

variable {ι : Sort*} {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A]

theorem op_iSup (S : ι → Subalgebra R A) : (iSup S).op = ⨆ i, (S i).op := Subalgebra.opEquiv.map_iSup _

