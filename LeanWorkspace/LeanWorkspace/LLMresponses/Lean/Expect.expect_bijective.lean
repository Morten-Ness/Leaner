FAIL
import Mathlib

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [Fintype ι] [Fintype κ]

variable [AddCommMonoid M] [Module ℚ≥0 M]

theorem expect_bijective (e : ι → κ) (he : Function.Bijective e) (f : ι → M) (g : κ → M)
    (h : ∀ i, f i = g (e i)) : 𝔼 i, f i = 𝔼 i, g i := by
  classical
  rw [show f = fun i => g (e i) by
    funext i
    exact h i]
  simp_rw [Finset.expect]
  rw [Finset.sum_univ_bijective e he.injective he.surjective]
  simp [Fintype.card_of_bijective he]
