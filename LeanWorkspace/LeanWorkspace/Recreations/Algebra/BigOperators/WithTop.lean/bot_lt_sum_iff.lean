import Mathlib

variable {ι M M₀ : Type*}

variable [AddCommMonoid M] {s : Finset ι} {f : ι → WithBot M}

variable [LT M]

theorem bot_lt_sum_iff : ⊥ < ∑ i ∈ s, f i ↔ ∀ i ∈ s, ⊥ < f i := by
  simp only [WithBot.bot_lt_iff_ne_bot, ne_eq, WithBot.sum_eq_bot_iff, not_exists, not_and]

