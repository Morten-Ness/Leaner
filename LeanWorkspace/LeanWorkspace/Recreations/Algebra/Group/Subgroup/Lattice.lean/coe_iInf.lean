import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem coe_iInf {ι : Sort*} {S : ι → Subgroup G} : (↑(⨅ i, S i) : Set G) = ⋂ i, S i := by
  simp only [iInf, Subgroup.coe_sInf, Set.biInter_range]

