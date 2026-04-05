import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocRing R]

theorem unop_iInf (S : ι → Subring Rᵐᵒᵖ) : (iInf S).unop = ⨅ i, (S i).unop := Subring.opEquiv.symm.map_iInf _

