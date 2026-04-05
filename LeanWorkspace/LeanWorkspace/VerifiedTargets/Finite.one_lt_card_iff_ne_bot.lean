import Mathlib

variable {G : Type*} [Group G]

variable {A : Type*} [AddGroup A]

variable (H K : Subgroup G)

theorem one_lt_card_iff_ne_bot [Finite H] : 1 < Nat.card H ↔ H ≠ ⊥ := lt_iff_not_ge.trans H.card_le_one_iff_eq_bot.not

