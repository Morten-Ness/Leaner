import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocSemiring R]

theorem unop_iInf (S : ι → Subsemiring Rᵐᵒᵖ) : (iInf S).unop = ⨅ i, (S i).unop := Subsemiring.opEquiv.symm.map_iInf _

