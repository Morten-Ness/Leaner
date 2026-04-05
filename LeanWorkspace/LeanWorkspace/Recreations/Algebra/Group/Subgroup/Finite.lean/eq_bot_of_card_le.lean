import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem eq_bot_of_card_le [Finite H] (h : Nat.card H ≤ 1) : H = ⊥ := let _ := Finite.card_le_one_iff_subsingleton.mp h
  eq_bot_of_subsingleton H

