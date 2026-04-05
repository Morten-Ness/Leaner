import Mathlib

section

variable {ι M M₀ : Type*}

variable [AddCommMonoid M] {s : Finset ι} {f : ι → WithBot M}

variable [LT M]

theorem bot_lt_sum_iff : ⊥ < ∑ i ∈ s, f i ↔ ∀ i ∈ s, ⊥ < f i := by
  simp only [WithBot.bot_lt_iff_ne_bot, ne_eq, WithBot.sum_eq_bot_iff, not_exists, not_and]

end

section

variable {ι M M₀ : Type*}

variable [CommMonoidWithZero M₀] [NoZeroDivisors M₀] [Nontrivial M₀] [DecidableEq M₀]
  {s : Finset ι} {f : ι → WithTop M₀} {i : ι}

theorem prod_eq_top_ex_top (h : ∏ j ∈ s, f j = ⊤) : ∃ i ∈ s, f i = ⊤ := by
  contrapose! h
  exact WithTop.prod_ne_top h

end

section

variable {ι M M₀ : Type*}

variable [CommMonoidWithZero M₀] [NoZeroDivisors M₀] [Nontrivial M₀] [DecidableEq M₀]
  {s : Finset ι} {f : ι → WithTop M₀} {i : ι}

theorem prod_eq_top_iff : ∏ j ∈ s, f j = ⊤ ↔ (∃ i ∈ s, f i = ⊤) ∧ (∀ i ∈ s, f i ≠ 0) := by
  constructor
  · exact fun h ↦ ⟨WithTop.prod_eq_top_ex_top h, fun _ ih ↦ WithTop.prod_eq_top_ne_zero ih h⟩
  · exact fun ⟨h, h'⟩ ↦ WithTop.prod_eq_top (Exists.choose_spec h).1 (Exists.choose_spec h).2 h'

end

section

variable {ι M M₀ : Type*}

variable [AddCommMonoid M] {s : Finset ι} {f : ι → WithBot M}

theorem sum_eq_bot_iff : ∑ i ∈ s, f i = ⊥ ↔ ∃ i ∈ s, f i = ⊥ := by
  induction s using Finset.cons_induction <;> simp [*]

end

section

variable {ι M M₀ : Type*}

variable [AddCommMonoid M] {s : Finset ι} {f : ι → WithBot M}

variable [LT M]

theorem sum_lt_bot (h : ∀ i ∈ s, f i ≠ ⊥) : ⊥ < ∑ i ∈ s, f i := WithBot.bot_lt_sum_iff.2 fun i hi ↦ WithBot.bot_lt_iff_ne_bot.2 (h i hi)

end
