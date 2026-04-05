import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

theorem _root_.Subgroup.inclusion_range {H K : Subgroup G} (h_le : H ≤ K) :
    (inclusion h_le).range = H.subgroupOf K := Subgroup.ext fun g => Set.ext_iff.mp (Set.range_inclusion h_le) g

