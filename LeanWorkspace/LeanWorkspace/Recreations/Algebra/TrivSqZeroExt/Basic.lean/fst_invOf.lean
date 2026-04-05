import Mathlib

open scoped RightActions

variable {R : Type u} {M : Type v}

variable [AddCommGroup M] [Semiring R] [Module Rᵐᵒᵖ M] [Module R M]

theorem fst_invOf (x : tsze R M) [Invertible x] [Invertible x.fst] : (⅟x).fst = ⅟(x.fst) := by
  letI := invertibleFstOfInvertible x
  convert (rfl : _ = ⅟x.fst)

