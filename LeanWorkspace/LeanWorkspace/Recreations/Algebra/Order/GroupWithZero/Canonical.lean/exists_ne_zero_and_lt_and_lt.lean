import Mathlib

variable {α β : Type*}

variable [LinearOrder α] {a b c : α} {x y : WithZero α}

theorem exists_ne_zero_and_lt_and_lt [NoMinOrder α] (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ z, z ≠ 0 ∧ z < x ∧ z < y := by
  obtain ⟨z', hnz', hzx, hzy⟩ := WithZero.exists_ne_zero_and_le_and_le hx hy
  obtain ⟨z, hnz, hlt⟩ := WithZero.exists_ne_zero_and_lt hnz'
  use z, hnz
  constructor <;> exact lt_of_lt_of_le hlt ‹z' ≤ _›

