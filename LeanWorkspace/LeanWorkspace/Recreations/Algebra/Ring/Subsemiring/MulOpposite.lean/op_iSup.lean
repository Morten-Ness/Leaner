import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocSemiring R]

theorem op_iSup (S : ι → Subsemiring R) : (iSup S).op = ⨆ i, (S i).op := Subsemiring.opEquiv.map_iSup _

