import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem mem_iSup_of_mem {ι : Sort*} {S : ι → Subgroup G} (i : ι) :
    ∀ {x : G}, x ∈ S i → x ∈ iSup S := have : S i ≤ iSup S := le_iSup _ _; fun h ↦ this h

