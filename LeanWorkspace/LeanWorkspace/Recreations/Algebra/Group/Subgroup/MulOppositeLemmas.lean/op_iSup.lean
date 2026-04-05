import Mathlib

variable {ι : Sort*} {G : Type*} [Group G]

theorem op_iSup (S : ι → Subgroup G) : (iSup S).op = ⨆ i, (S i).op := opEquiv.map_iSup _

