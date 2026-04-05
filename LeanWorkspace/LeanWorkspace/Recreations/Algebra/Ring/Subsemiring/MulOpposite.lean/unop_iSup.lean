import Mathlib

variable {ι : Sort*} {R : Type*} [NonAssocSemiring R]

theorem unop_iSup (S : ι → Subsemiring Rᵐᵒᵖ) : (iSup S).unop = ⨆ i, (S i).unop := Subsemiring.opEquiv.symm.map_iSup _

