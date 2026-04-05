import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem mem_sSup_of_mem {S : Set (Subgroup G)} {s : Subgroup G} (hs : s ∈ S) :
    ∀ {x : G}, x ∈ s → x ∈ sSup S := have : s ≤ sSup S := le_sSup hs; fun h ↦ this h

