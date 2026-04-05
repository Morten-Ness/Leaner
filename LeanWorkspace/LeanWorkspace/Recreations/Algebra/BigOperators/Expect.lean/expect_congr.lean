import Mathlib

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [AddCommMonoid M] [Module ℚ≥0 M] [AddCommMonoid N] [Module ℚ≥0 N] {s t : Finset ι}
  {f g : ι → M} {p q : ι → Prop} [DecidablePred p] [DecidablePred q]

theorem expect_congr {t : Finset ι} (hst : s = t) (h : ∀ i ∈ t, f i = g i) :
    𝔼 i ∈ s, f i = 𝔼 i ∈ t, g i := by rw [expect, expect, Finset.sum_congr hst h, hst]

