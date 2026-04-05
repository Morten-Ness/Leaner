import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem subgroupOf_inj {H₁ H₂ K : Subgroup G} :
    H₁.subgroupOf K = H₂.subgroupOf K ↔ H₁ ⊓ K = H₂ ⊓ K := by
  simpa only [SetLike.ext_iff, mem_inf, Subgroup.mem_subgroupOf, and_congr_left_iff] using Subtype.forall

