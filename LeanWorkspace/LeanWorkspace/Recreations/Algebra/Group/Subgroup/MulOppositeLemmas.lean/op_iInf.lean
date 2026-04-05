import Mathlib

variable {ι : Sort*} {G : Type*} [Group G]

theorem op_iInf (S : ι → Subgroup G) : (iInf S).op = ⨅ i, (S i).op := opEquiv.map_iInf _

