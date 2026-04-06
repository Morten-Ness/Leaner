import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem mem_sSup_of_mem {S : Set (Subgroup G)} {s : Subgroup G} (hs : s ∈ S) :
    ∀ {x : G}, x ∈ s → x ∈ sSup S := by
  intro x hx
  exact Subgroup.mem_sSup_of_mem hs hx
