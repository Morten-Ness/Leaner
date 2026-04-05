import Mathlib

variable {M A B : Type*}

variable [Monoid M] {a : M}

variable {S : Submonoid M} [Fintype S]

theorem eq_bot_of_card_le (h : card S ≤ 1) : S = ⊥ := let _ := card_le_one_iff_subsingleton.mp h
  eq_bot_of_subsingleton S

