import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem inf_subgroupOf_right (H K : Subgroup G) : (H ⊓ K).subgroupOf K = H.subgroupOf K := Subgroup.subgroupOf_inj.2 (inf_right_idem _ _)

