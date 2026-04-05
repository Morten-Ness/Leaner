import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem inf_subgroupOf_left (H K : Subgroup G) : (K ⊓ H).subgroupOf K = H.subgroupOf K := by
  rw [inf_comm, Subgroup.inf_subgroupOf_right]

