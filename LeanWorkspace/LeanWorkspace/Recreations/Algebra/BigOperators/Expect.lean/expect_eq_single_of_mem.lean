import Mathlib

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [AddCommMonoid M] [Module ℚ≥0 M] [AddCommMonoid N] [Module ℚ≥0 N] {s t : Finset ι}
  {f g : ι → M} {p q : ι → Prop} [DecidablePred p] [DecidablePred q]

theorem expect_eq_single_of_mem (i : ι) (hi : i ∈ s) (h : ∀ j ∈ s, j ≠ i → f j = 0) :
    𝔼 i ∈ s, f i = f i /ℚ #s := by rw [expect, sum_eq_single_of_mem _ hi h]

