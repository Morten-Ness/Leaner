import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem normal_subgroupOf_sup_of_le_normalizer {H N : Subgroup G}
    (hLE : H ≤ normalizer N) : (N.subgroupOf (H ⊔ N)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right]
  exact sup_le hLE le_normalizer

