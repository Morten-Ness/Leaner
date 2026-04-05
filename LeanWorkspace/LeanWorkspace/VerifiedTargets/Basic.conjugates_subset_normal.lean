import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem conjugates_subset_normal {N : Subgroup G} [tn : N.Normal] {a : G} (h : a ∈ N) :
    conjugatesOf a ⊆ N := by
  rintro a hc
  obtain ⟨c, rfl⟩ := isConj_iff.1 hc
  exact tn.conj_mem a h c

