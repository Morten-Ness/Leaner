import Mathlib

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [AddCommMonoid M] [Module ℚ≥0 M] [AddCommMonoid N] [Module ℚ≥0 N] {s t : Finset ι}
  {f g : ι → M} {p q : ι → Prop} [DecidablePred p] [DecidablePred q]

variable {t : Finset κ} {g : κ → M}

theorem expect_nbij (i : ι → κ) (hi : ∀ a ∈ s, i a ∈ t) (h : ∀ a ∈ s, f a = g (i a))
    (i_inj : (s : Set ι).InjOn i) (i_surj : (s : Set ι).SurjOn i t) :
    𝔼 i ∈ s, f i = 𝔼 i ∈ t, g i := by
  simp_rw [expect, card_nbij i hi i_inj i_surj, sum_nbij i hi i_inj i_surj h]

