import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem card_le_one_iff_eq_bot [Finite H] : Nat.card H ≤ 1 ↔ H = ⊥ := ⟨H.eq_bot_of_card_le, fun h => by simp [h]⟩

