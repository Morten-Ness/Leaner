import Mathlib

variable {R ι : Type*}

variable [AddMonoidWithOne R]

variable [CharP R 2]

theorem natCast_cases (n : ℕ) : (n : R) = 0 ∨ (n : R) = 1 := CharTwo.range_natCast.le (Set.mem_range_self _)

