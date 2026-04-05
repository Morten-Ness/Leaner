import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

theorem mem_sup_right {S T : Subgroup G} : ∀ {x : G}, x ∈ T → x ∈ S ⊔ T := have : T ≤ S ⊔ T := le_sup_right; fun h ↦ this h

