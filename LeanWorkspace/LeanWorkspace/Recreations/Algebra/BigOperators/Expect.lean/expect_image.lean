import Mathlib

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [AddCommMonoid M] [Module ℚ≥0 M] [AddCommMonoid N] [Module ℚ≥0 N] {s t : Finset ι}
  {f g : ι → M} {p q : ι → Prop} [DecidablePred p] [DecidablePred q]

variable {t : Finset κ} {g : κ → M}

theorem expect_image [DecidableEq ι] {m : κ → ι} (hm : (t : Set κ).InjOn m) :
    𝔼 i ∈ t.image m, f i = 𝔼 i ∈ t, f (m i) := by
  simp_rw [expect, card_image_of_injOn hm, sum_image hm]

