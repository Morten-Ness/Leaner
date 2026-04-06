FAIL
import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

theorem subgroupOf_range_eq_of_le {G₁ G₂ : Type*} [Group G₁] [Group G₂] {K : Subgroup G₂}
    (f : G₁ →* G₂) (h : f.range ≤ K) :
    f.range.subgroupOf K = (f.codRestrict K fun x => h ⟨x, rfl⟩).range := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxR, hxK⟩
    rcases hxR with ⟨y, hy⟩
    refine ⟨y, ?_⟩
    apply Subtype.ext
    exact hy
  · intro hx
    rcases hx with ⟨y, hy⟩
    refine ⟨?_, ?_⟩
    · exact ⟨y, rfl⟩
    · have hy' : f y = x := by
        exact congrArg Subtype.val hy
      simpa [hy'] using h ⟨y, rfl⟩
