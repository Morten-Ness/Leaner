import Mathlib

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [AddCommMonoid M] [Module ℚ≥0 M] [AddCommMonoid N] [Module ℚ≥0 N] {s t : Finset ι}
  {f g : ι → M} {p q : ι → Prop} [DecidablePred p] [DecidablePred q]

variable {t : Finset κ} {g : κ → M}

theorem expect_bij (i : ∀ a ∈ s, κ) (hi : ∀ a ha, i a ha ∈ t) (h : ∀ a ha, f a = g (i a ha))
    (i_inj : ∀ a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂)
    (i_surj : ∀ b ∈ t, ∃ a ha, i a ha = b) : 𝔼 i ∈ s, f i = 𝔼 i ∈ t, g i := by
  simp_rw [expect, card_bij i hi i_inj i_surj, sum_bij i hi i_inj i_surj h]

