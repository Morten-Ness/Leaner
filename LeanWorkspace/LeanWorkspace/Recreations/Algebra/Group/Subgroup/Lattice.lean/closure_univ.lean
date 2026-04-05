import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem closure_univ : Subgroup.closure (Set.univ : Set G) = ⊤ := @Subgroup.coe_top G _ ▸ Subgroup.closure_eq ⊤

