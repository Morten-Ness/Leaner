import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem mem_subgroupOf {H K : Subgroup G} {h : K} : h ∈ H.subgroupOf K ↔ (h : G) ∈ H := Iff.rfl

-- TODO(kmill): use `K ⊓ H` order for RHS to match `Subtype.image_preimage_coe`

