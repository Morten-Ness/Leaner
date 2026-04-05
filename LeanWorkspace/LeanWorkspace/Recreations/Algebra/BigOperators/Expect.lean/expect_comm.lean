import Mathlib

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [AddCommMonoid M] [Module ℚ≥0 M] [AddCommMonoid N] [Module ℚ≥0 N] {s t : Finset ι}
  {f g : ι → M} {p q : ι → Prop} [DecidablePred p] [DecidablePred q]

theorem expect_comm (s : Finset ι) (t : Finset κ) (f : ι → κ → M) :
    𝔼 i ∈ s, 𝔼 j ∈ t, f i j = 𝔼 j ∈ t, 𝔼 i ∈ s, f i j := by
  rw [expect, expect, ← Finset.expect_sum_comm, ← Finset.expect_sum_comm, expect, expect, smul_comm, sum_comm]

