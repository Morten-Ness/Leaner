import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem map_top_of_surjective (f : G →* N) (h : Function.Surjective f) : Subgroup.map f ⊤ = ⊤ := by
  ext n
  constructor
  · intro _
    simp
  · intro _
    rcases h n with ⟨g, rfl⟩
    exact ⟨g, by simp, rfl⟩
