import Mathlib

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [AddCommMonoid M] [Module ℚ≥0 M] [AddCommMonoid N] [Module ℚ≥0 N] {s t : Finset ι}
  {f g : ι → M} {p q : ι → Prop} [DecidablePred p] [DecidablePred q]

variable {t : Finset κ} {g : κ → M}

theorem expect_bij' (i : ∀ a ∈ s, κ) (j : ∀ a ∈ t, ι) (hi : ∀ a ha, i a ha ∈ t)
    (hj : ∀ a ha, j a ha ∈ s) (left_inv : ∀ a ha, j (i a ha) (hi a ha) = a)
    (right_inv : ∀ a ha, i (j a ha) (hj a ha) = a) (h : ∀ a ha, f a = g (i a ha)) :
    𝔼 i ∈ s, f i = 𝔼 i ∈ t, g i := by
  simp_rw [expect, card_bij' i j hi hj left_inv right_inv, sum_bij' i j hi hj left_inv right_inv h]

