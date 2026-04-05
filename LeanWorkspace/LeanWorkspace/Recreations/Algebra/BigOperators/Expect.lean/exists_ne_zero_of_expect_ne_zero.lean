import Mathlib

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [AddCommMonoid M] [Module ℚ≥0 M] [AddCommMonoid N] [Module ℚ≥0 N] {s t : Finset ι}
  {f g : ι → M} {p q : ι → Prop} [DecidablePred p] [DecidablePred q]

theorem exists_ne_zero_of_expect_ne_zero (h : 𝔼 i ∈ s, f i ≠ 0) : ∃ i ∈ s, f i ≠ 0 := by
  contrapose! h; exact Finset.expect_eq_zero h

