import Mathlib

open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

variable {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem bot_prod_bot : (⊥ : Subgroup G).prod (⊥ : Subgroup N) = ⊥ := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxG, hxN⟩
    simp at hxG hxN
    ext <;> assumption
  · intro hx
    simp at hx
    simp [hx]
