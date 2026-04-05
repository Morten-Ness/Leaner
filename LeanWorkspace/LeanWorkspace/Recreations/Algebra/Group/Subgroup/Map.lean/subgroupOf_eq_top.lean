import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem subgroupOf_eq_top {H K : Subgroup G} : H.subgroupOf K = ⊤ ↔ K ≤ H := by
  rw [← Subgroup.top_subgroupOf, Subgroup.subgroupOf_inj, top_inf_eq, inf_eq_right]

