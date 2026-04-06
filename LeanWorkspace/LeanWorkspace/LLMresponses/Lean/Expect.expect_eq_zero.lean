import Mathlib

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [AddCommMonoid M] [Module ℚ≥0 M] [AddCommMonoid N] [Module ℚ≥0 N] {s t : Finset ι}
  {f g : ι → M} {p q : ι → Prop} [DecidablePred p] [DecidablePred q]

theorem expect_eq_zero (h : ∀ i ∈ s, f i = 0) : 𝔼 i ∈ s, f i = 0 := by
  classical
  by_cases hs : s = ∅
  · simp [Finset.expect, hs]
  · simp [Finset.expect, hs]
    exact Finset.sum_eq_zero fun i hi => h i (by simpa using hi)
