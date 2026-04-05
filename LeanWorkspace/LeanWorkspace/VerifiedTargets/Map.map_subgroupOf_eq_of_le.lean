import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem map_subgroupOf_eq_of_le {H K : Subgroup G} (h : H ≤ K) :
    (H.subgroupOf K).map K.subtype = H := by
  rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left]

