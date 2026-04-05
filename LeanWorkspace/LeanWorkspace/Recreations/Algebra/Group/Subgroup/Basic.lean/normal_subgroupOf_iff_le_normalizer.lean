import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {H K : Subgroup G}

variable {N : Type*} [Group N]

theorem normal_subgroupOf_iff_le_normalizer (h : H ≤ K) :
    (H.subgroupOf K).Normal ↔ K ≤ normalizer H := by
  rw [← subgroupOf_eq_top, Subgroup.subgroupOf_normalizer_eq h, Subgroup.normalizer_eq_top_iff]

