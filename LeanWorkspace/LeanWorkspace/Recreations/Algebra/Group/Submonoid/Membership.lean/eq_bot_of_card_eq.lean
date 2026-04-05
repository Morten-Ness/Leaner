import Mathlib

variable {M A B : Type*}

variable [Monoid M] {a : M}

variable {S : Submonoid M} [Fintype S]

theorem eq_bot_of_card_eq (h : card S = 1) : S = ⊥ := S.eq_bot_of_card_le (le_of_eq h)

