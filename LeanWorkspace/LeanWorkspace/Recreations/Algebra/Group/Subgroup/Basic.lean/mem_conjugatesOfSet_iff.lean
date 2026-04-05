import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem mem_conjugatesOfSet_iff {x : G} : x ∈ Group.conjugatesOfSet s ↔ ∃ a ∈ s, IsConj a x := by
  rw [Group.conjugatesOfSet, Set.mem_iUnion₂]
  simp only [conjugatesOf, isConj_iff, Set.mem_setOf_eq, exists_prop]

