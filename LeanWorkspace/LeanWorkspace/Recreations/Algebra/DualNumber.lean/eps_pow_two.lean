import Mathlib

variable {R A B : Type*}

theorem eps_pow_two [Semiring R] : (ε : R[ε]) ^ 2 = 0 := by
  simp [pow_two]

