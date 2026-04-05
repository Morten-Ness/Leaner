import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocRing R]

theorem unop_iSup (S : ι → Subring Rᵐᵒᵖ) : (iSup S).unop = ⨆ i, (S i).unop := Subring.opEquiv.symm.map_iSup _

