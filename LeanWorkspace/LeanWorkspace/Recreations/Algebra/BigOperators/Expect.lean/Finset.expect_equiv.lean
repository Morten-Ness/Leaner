import Mathlib

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [AddCommMonoid M] [Module ℚ≥0 M] [AddCommMonoid N] [Module ℚ≥0 N] {s t : Finset ι}
  {f g : ι → M} {p q : ι → Prop} [DecidablePred p] [DecidablePred q]

variable {t : Finset κ} {g : κ → M}

theorem expect_equiv (e : ι ≃ κ) (hst : ∀ i, i ∈ s ↔ e i ∈ t) (hfg : ∀ i ∈ s, f i = g (e i)) :
    𝔼 i ∈ s, f i = 𝔼 i ∈ t, g i := by simp_rw [expect, card_equiv e hst, sum_equiv e hst hfg]

