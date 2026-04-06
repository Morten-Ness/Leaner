import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

theorem range_one : (1 : G →* N).range = ⊥ := by
  ext n
  constructor
  · intro hn
    rcases hn with ⟨g, rfl⟩
    simp
  · intro hn
    rw [Subgroup.mem_bot] at hn
    refine ⟨1, ?_⟩
    simp [hn]
