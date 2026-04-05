import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} [Group N]

theorem inf_subgroupOf_inf_normal_of_left {A' A : Subgroup G} (B : Subgroup G)
    [hN : (A'.subgroupOf A).Normal] : ((A' ⊓ B).subgroupOf (A ⊓ B)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer_inf] at hN ⊢
  rw [inf_inf_inf_comm, inf_idem]
  exact le_trans (inf_le_inf hN B.le_normalizer) Subgroup.inf_normalizer_le_normalizer_inf

