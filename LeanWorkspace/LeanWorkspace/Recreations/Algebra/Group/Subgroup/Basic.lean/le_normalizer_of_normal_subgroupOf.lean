import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {H K : Subgroup G}

variable {N : Type*} [Group N]

theorem le_normalizer_of_normal_subgroupOf [hK : (H.subgroupOf K).Normal] (HK : H ≤ K) :
    K ≤ normalizer H := (Subgroup.normal_subgroupOf_iff_le_normalizer HK).mp hK

