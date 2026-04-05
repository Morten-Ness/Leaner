import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem eq_top_of_le_card [Finite G] (h : Nat.card G ≤ Nat.card H) : H = ⊤ := Subgroup.eq_of_le_of_card_ge le_top (Nat.card_congr (Equiv.Set.univ G) ▸ h)

