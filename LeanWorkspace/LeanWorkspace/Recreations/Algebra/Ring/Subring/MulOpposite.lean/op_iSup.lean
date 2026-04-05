import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocRing R]

theorem op_iSup (S : ι → Subring R) : (iSup S).op = ⨆ i, (S i).op := Subring.opEquiv.map_iSup _

