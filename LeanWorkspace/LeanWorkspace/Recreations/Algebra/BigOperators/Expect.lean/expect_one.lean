import Mathlib

open scoped Pointwise BigOperators

variable {ι κ M N : Type*}

variable [Fintype ι] [Fintype κ]

variable [Semiring M] [Module ℚ≥0 M]

theorem expect_one [Nonempty ι] : 𝔼 _i : ι, (1 : M) = 1 := Fintype.expect_const _

