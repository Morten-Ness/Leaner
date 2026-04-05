import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem mem_iInf {ι : Sort*} {S : ι → Subgroup G} {x : G} : x ∈ ⨅ i, S i ↔ ∀ i, x ∈ S i := by
  simp only [iInf, Subgroup.mem_sInf, Set.forall_mem_range]

