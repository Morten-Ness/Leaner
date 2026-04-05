import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem mem_sup_left {S T : Subgroup G} : ∀ {x : G}, x ∈ S → x ∈ S ⊔ T := have : S ≤ S ⊔ T := le_sup_left; fun h ↦ this h

