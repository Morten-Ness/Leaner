import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem eq_bot_of_card_eq (h : Nat.card H = 1) : H = ⊥ := let _ := (Nat.card_eq_one_iff_unique.mp h).1
  eq_bot_of_subsingleton H

