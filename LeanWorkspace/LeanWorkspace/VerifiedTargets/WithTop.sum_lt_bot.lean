import Mathlib

variable {ι M M₀ : Type*}

variable [AddCommMonoid M] {s : Finset ι} {f : ι → WithBot M}

variable [LT M]

theorem sum_lt_bot (h : ∀ i ∈ s, f i ≠ ⊥) : ⊥ < ∑ i ∈ s, f i := WithBot.bot_lt_sum_iff.2 fun i hi ↦ WithBot.bot_lt_iff_ne_bot.2 (h i hi)

