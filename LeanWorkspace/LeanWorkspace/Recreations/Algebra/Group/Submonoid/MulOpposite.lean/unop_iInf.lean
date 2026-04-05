import Mathlib

variable {ι : Sort*} {M : Type*} [MulOneClass M]

theorem unop_iInf (S : ι → Submonoid Mᵐᵒᵖ) : (iInf S).unop = ⨅ i, (S i).unop := Submonoid.opEquiv.symm.map_iInf _

