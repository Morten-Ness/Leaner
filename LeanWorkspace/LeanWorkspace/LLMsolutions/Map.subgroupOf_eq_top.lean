import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem subgroupOf_eq_top {H K : Subgroup G} : H.subgroupOf K = ⊤ ↔ K ≤ H := by
  constructor
  · intro h x hxK
    have hxTop : ⟨x, hxK⟩ ∈ H.subgroupOf K := by
      rw [h]
      exact Subgroup.mem_top _
    exact hxTop
  · intro h
    ext x
    constructor
    · intro hx
      exact Subgroup.mem_top x
    · intro _
      exact h x.2
