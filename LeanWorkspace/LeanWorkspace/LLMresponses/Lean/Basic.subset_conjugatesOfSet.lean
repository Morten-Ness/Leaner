import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {s : Set G}

theorem subset_conjugatesOfSet : s ⊆ Group.conjugatesOfSet s := by
  intro a ha
  rw [Group.mem_conjugatesOfSet_iff]
  exact ⟨a, ha, 1, by simp⟩
