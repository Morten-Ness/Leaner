import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem normal_subgroupOf_of_le_normalizer {H N : Subgroup G}
    (hLE : H ≤ normalizer N) : (N.subgroupOf H).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer_inf]
  exact (le_inf hLE H.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf

