import Mathlib

variable {ι : Sort*} {G : Type*} [Group G]

theorem unop_iInf (S : ι → Subgroup Gᵐᵒᵖ) : (iInf S).unop = ⨅ i, (S i).unop := opEquiv.symm.map_iInf _

