import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocRing R]

theorem op_iInf (S : ι → Subring R) : (iInf S).op = ⨅ i, (S i).op := Subring.opEquiv.map_iInf _

