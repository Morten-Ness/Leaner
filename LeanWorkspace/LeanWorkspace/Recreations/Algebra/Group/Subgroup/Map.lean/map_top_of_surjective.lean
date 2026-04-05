import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem map_top_of_surjective (f : G →* N) (h : Function.Surjective f) : Subgroup.map f ⊤ = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy⟩ := h x
  exact ⟨y, trivial, hy⟩

