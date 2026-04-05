import Mathlib

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [Fintype ι] [Fintype κ]

variable [AddCommMonoid M] [Module ℚ≥0 M]

variable [DecidableEq ι]

theorem expect_ite_eq (i : ι) (f : ι → M) :
    𝔼 j, (if i = j then f j else 0) = f i /ℚ card ι := by simp

