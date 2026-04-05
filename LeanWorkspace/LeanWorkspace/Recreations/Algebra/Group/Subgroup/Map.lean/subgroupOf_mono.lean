import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem subgroupOf_mono {H₁ H₂ : Subgroup G} (H₃ : Subgroup G) (h : H₁ ≤ H₂) :
    H₁.subgroupOf H₃ ≤ H₂.subgroupOf H₃ := Subgroup.comap_mono h

