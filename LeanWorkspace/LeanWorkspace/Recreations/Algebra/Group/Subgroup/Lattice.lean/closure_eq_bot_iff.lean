import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem closure_eq_bot_iff : Subgroup.closure k = ⊥ ↔ k ⊆ {1} := le_bot_iff.symm.trans <| Subgroup.closure_le _

