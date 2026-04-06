import Mathlib

open scoped Int Relator

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

variable {k : Set G}

variable {N : Type*} [Group N] {P : Type*} [Group P]

theorem prod_mono : ((· ≤ ·) ⇒ (· ≤ ·) ⇒ (· ≤ ·)) (@Subgroup.prod G _ N _) (@Subgroup.prod G _ N _) := by
  intro H₁ H₂ hH K₁ K₂ hK
  intro x hx
  exact ⟨hH hx.1, hK hx.2⟩
