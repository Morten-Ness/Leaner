import Mathlib

variable {ι M M₀ : Type*}

variable [AddCommMonoid M] {s : Finset ι} {f : ι → WithBot M}

theorem sum_eq_bot_iff : ∑ i ∈ s, f i = ⊥ ↔ ∃ i ∈ s, f i = ⊥ := by
  induction s using Finset.cons_induction <;> simp [*]

