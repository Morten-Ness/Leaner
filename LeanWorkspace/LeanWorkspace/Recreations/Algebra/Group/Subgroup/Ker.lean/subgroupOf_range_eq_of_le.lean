import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

theorem subgroupOf_range_eq_of_le {G₁ G₂ : Type*} [Group G₁] [Group G₂] {K : Subgroup G₂}
    (f : G₁ →* G₂) (h : f.range ≤ K) :
    f.range.subgroupOf K = (f.codRestrict K fun x => h ⟨x, rfl⟩).range := by
  ext k
  refine exists_congr ?_
  simp [Subtype.ext_iff]

