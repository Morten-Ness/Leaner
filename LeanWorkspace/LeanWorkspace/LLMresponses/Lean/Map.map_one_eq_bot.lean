import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G) {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem map_one_eq_bot : K.map (1 : G →* N) = ⊥ := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨y, hy, rfl⟩
    simp
  · intro hx
    rcases show x = 1 from by simpa using hx with rfl
    exact ⟨1, K.one_mem, by simp⟩
