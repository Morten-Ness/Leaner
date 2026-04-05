import Mathlib

variable {ι : Sort*} {M : Type*} [MulOneClass M]

theorem unop_iSup (S : ι → Submonoid Mᵐᵒᵖ) : (iSup S).unop = ⨆ i, (S i).unop := Submonoid.opEquiv.symm.map_iSup _

