import Mathlib

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [Fintype ι] [Fintype κ]

variable [AddCommMonoid M] [Module ℚ≥0 M]

variable [DecidableEq ι]

theorem expect_dite_eq (i : ι) (f : ∀ j, i = j → M) :
    𝔼 j, (if h : i = j then f j h else 0) = f i rfl /ℚ card ι := by simp

