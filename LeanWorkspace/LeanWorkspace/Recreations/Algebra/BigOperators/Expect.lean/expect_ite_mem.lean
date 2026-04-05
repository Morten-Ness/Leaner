import Mathlib

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [AddCommMonoid M] [Module ℚ≥0 M] [AddCommMonoid N] [Module ℚ≥0 N] {s t : Finset ι}
  {f g : ι → M} {p q : ι → Prop} [DecidablePred p] [DecidablePred q]

variable [DecidableEq ι]

theorem expect_ite_mem (s t : Finset ι) (f : ι → M) :
    𝔼 i ∈ s, (if i ∈ t then f i else 0) = (#(s ∩ t) / #s : ℚ≥0) • 𝔼 i ∈ s ∩ t, f i := by
  obtain hst | hst := (s ∩ t).eq_empty_or_nonempty
  · simp [expect, hst]
  · simp [expect, smul_smul, ← inv_mul_eq_div, hst.card_ne_zero]

