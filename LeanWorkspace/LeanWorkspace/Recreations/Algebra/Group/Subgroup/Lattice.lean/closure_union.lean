import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem closure_union (s t : Set G) : Subgroup.closure (s ∪ t) = Subgroup.closure s ⊔ Subgroup.closure t := (Subgroup.gi G).gc.l_sup

