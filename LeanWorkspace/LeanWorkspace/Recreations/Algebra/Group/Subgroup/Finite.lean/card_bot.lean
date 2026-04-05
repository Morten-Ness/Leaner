import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem card_bot : Nat.card (⊥ : Subgroup G) = 1 := by simp

