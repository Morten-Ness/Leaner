import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {H K : Subgroup G}

variable {N : Type*} [Group N]

theorem normal_subgroupOf_iff_le_normalizer_inf :
    (H.subgroupOf K).Normal ↔ K ≤ normalizer (H ⊓ K : Subgroup G) := inf_subgroupOf_right H K ▸ Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right

