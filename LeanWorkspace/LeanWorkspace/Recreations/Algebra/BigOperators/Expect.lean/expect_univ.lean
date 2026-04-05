import Mathlib

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [AddCommMonoid M] [Module ℚ≥0 M] [AddCommMonoid N] [Module ℚ≥0 N] {s t : Finset ι}
  {f g : ι → M} {p q : ι → Prop} [DecidablePred p] [DecidablePred q]

theorem expect_univ [Fintype ι] : 𝔼 i, f i = (∑ i, f i) /ℚ Fintype.card ι := by
  rw [expect, card_univ]

