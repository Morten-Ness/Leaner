import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem subgroupOf_eq_bot {H K : Subgroup G} : H.subgroupOf K = ⊥ ↔ Disjoint H K := by
  rw [disjoint_iff, ← Subgroup.bot_subgroupOf, Subgroup.subgroupOf_inj, bot_inf_eq]

