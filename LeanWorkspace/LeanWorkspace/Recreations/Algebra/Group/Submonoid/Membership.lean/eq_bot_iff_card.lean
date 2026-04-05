import Mathlib

variable {M A B : Type*}

variable [Monoid M] {a : M}

variable {S : Submonoid M} [Fintype S]

theorem eq_bot_iff_card : S = ⊥ ↔ card S = 1 := ⟨by rintro rfl; exact Submonoid.card_bot, Submonoid.eq_bot_of_card_eq⟩

