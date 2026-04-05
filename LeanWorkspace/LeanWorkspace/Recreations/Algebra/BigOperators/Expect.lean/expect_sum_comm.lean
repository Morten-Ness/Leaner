import Mathlib

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [AddCommMonoid M] [Module ℚ≥0 M] [AddCommMonoid N] [Module ℚ≥0 N] {s t : Finset ι}
  {f g : ι → M} {p q : ι → Prop} [DecidablePred p] [DecidablePred q]

theorem expect_sum_comm (s : Finset ι) (t : Finset κ) (f : ι → κ → M) :
    𝔼 i ∈ s, ∑ j ∈ t, f i j = ∑ j ∈ t, 𝔼 i ∈ s, f i j := by
  simpa only [expect, smul_sum] using sum_comm

