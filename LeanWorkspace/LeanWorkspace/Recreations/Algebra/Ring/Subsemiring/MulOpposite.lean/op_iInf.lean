import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocSemiring R]

theorem op_iInf (S : ι → Subsemiring R) : (iInf S).op = ⨅ i, (S i).op := Subsemiring.opEquiv.map_iInf _

