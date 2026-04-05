import Mathlib

variable {ι : Sort*} {M : Type*} [Mul M]

theorem unop_iSup (S : ι → Subsemigroup Mᵐᵒᵖ) : (iSup S).unop = ⨆ i, (S i).unop := Subsemigroup.opEquiv.symm.map_iSup _

