import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {H K : Subgroup G}

variable {N : Type*} [Group N]

theorem subgroupOf_normalizer_eq {H N : Subgroup G} (h : H ≤ N) :
    (normalizer H).subgroupOf N = normalizer (H.subgroupOf N) := Subgroup.comap_normalizer_eq_of_le_range (h.trans_eq N.range_subtype.symm)

