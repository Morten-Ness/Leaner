import Mathlib

variable {K L : Type*}

variable [DivisionSemiring K] {a b c d : K}

theorem div_add' (a b c : K) (hc : c ≠ 0) : a / c + b = (a + b * c) / c := by
  rwa [add_comm, add_div', add_comm]

