import Mathlib

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [AddCommMonoid M] [Module ℚ≥0 M] [AddCommMonoid N] [Module ℚ≥0 N] {s t : Finset ι}
  {f g : ι → M} {p q : ι → Prop} [DecidablePred p] [DecidablePred q]

variable {t : Finset κ} {g : κ → M}

theorem expect_product (s : Finset ι) (t : Finset κ) (f : ι × κ → M) :
    𝔼 x ∈ s ×ˢ t, f x = 𝔼 i ∈ s, 𝔼 j ∈ t, f (i, j) := by
  simp only [expect, card_product, sum_product, smul_sum, mul_inv, mul_smul, Nat.cast_mul]

