import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem closure_empty : Subgroup.closure (∅ : Set G) = ⊥ := (Subgroup.gi G).gc.l_bot

