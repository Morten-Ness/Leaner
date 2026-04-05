import Mathlib

variable {ι : Sort*} {M : Type*} [Mul M]

theorem unop_iInf (S : ι → Subsemigroup Mᵐᵒᵖ) : (iInf S).unop = ⨅ i, (S i).unop := Subsemigroup.opEquiv.symm.map_iInf _

