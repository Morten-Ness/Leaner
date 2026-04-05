import Mathlib

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [AddCommMonoid M] [Module ℚ≥0 M] [AddCommMonoid N] [Module ℚ≥0 N] {s t : Finset ι}
  {f g : ι → M} {p q : ι → Prop} [DecidablePred p] [DecidablePred q]

variable {t : Finset κ} {g : κ → M}

theorem expect_nbij' (i : ι → κ) (j : κ → ι) (hi : ∀ a ∈ s, i a ∈ t) (hj : ∀ a ∈ t, j a ∈ s)
    (left_inv : ∀ a ∈ s, j (i a) = a) (right_inv : ∀ a ∈ t, i (j a) = a)
    (h : ∀ a ∈ s, f a = g (i a)) : 𝔼 i ∈ s, f i = 𝔼 i ∈ t, g i := by
  simp_rw [expect, card_nbij' i j hi hj left_inv right_inv,
    sum_nbij' i j hi hj left_inv right_inv h]

