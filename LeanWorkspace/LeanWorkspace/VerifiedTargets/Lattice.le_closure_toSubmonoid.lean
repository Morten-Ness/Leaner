import Mathlib

open scoped Int

variable {G : Type*} [Group G]

variable (H K : Subgroup G)

variable {k : Set G}

theorem le_closure_toSubmonoid (S : Set G) : Submonoid.closure S ≤ (Subgroup.closure S).toSubmonoid := Submonoid.closure_le.2 Subgroup.subset_closure

