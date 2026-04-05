import Mathlib

variable {ι : Sort*} {G : Type*} [Group G]

theorem unop_iSup (S : ι → Subgroup Gᵐᵒᵖ) : (iSup S).unop = ⨆ i, (S i).unop := opEquiv.symm.map_iSup _

