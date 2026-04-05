import Mathlib

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [AddCommMonoid M] [Module ℚ≥0 M] [AddCommMonoid N] [Module ℚ≥0 N] {s t : Finset ι}
  {f g : ι → M} {p q : ι → Prop} [DecidablePred p] [DecidablePred q]

theorem expect_ite_zero (s : Finset ι) (p : ι → Prop) [DecidablePred p]
    (h : ∀ i ∈ s, ∀ j ∈ s, p i → p j → i = j) (a : M) :
    𝔼 i ∈ s, ite (p i) a 0 = ite (∃ i ∈ s, p i) (a /ℚ #s) 0 := by
  split_ifs <;> simp [expect, sum_ite_zero _ _ h, *]

