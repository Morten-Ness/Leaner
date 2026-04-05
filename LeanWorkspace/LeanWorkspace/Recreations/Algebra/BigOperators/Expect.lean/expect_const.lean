import Mathlib

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [Fintype ι] [Fintype κ]

variable [AddCommMonoid M] [Module ℚ≥0 M]

theorem expect_const [Nonempty ι] (a : M) : 𝔼 _i : ι, a = a := Finset.expect_const univ_nonempty _

