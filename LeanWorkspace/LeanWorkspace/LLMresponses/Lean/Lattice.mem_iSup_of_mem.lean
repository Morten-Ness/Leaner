import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem mem_iSup_of_mem {ι : Sort*} {S : ι → Subgroup G} (i : ι) :
    ∀ {x : G}, x ∈ S i → x ∈ iSup S := by
  intro x hx
  exact (show S i ≤ iSup S from le_iSup S i) hx
