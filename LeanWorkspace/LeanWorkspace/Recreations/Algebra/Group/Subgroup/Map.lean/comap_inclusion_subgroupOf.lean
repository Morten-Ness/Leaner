import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem comap_inclusion_subgroupOf {K₁ K₂ : Subgroup G} (h : K₁ ≤ K₂) (H : Subgroup G) :
    (H.subgroupOf K₂).comap (inclusion h) = H.subgroupOf K₁ := rfl

