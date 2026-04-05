import Mathlib

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [Fintype ι] [Fintype κ]

variable [AddCommMonoid M] [Module ℚ≥0 M]

theorem expect_ite_zero (p : ι → Prop) [DecidablePred p] (h : ∀ i j, p i → p j → i = j) (a : M) :
    𝔼 i, ite (p i) a 0 = ite (∃ i, p i) (a /ℚ Fintype.card ι) 0 := by
  simp [Finset.expect_ite_zero Finset.univ p (by simpa using h)]

