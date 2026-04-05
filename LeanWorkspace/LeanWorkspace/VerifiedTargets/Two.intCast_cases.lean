import Mathlib

variable {R ι : Type*}

variable [Ring R] [CharP R 2]

theorem intCast_cases (n : ℤ) : (n : R) = 0 ∨ (n : R) = 1 := (Set.ext_iff.1 CharTwo.range_intCast _).1 (Set.mem_range_self _)

