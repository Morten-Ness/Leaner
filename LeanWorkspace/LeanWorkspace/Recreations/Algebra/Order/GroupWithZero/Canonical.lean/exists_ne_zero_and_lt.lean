import Mathlib

variable {α β : Type*}

variable [Preorder α] [Preorder β] {x y : WithZero α} {a b : α}

theorem exists_ne_zero_and_lt [NoMinOrder α] (hx : x ≠ 0) :
    ∃ y, y ≠ 0 ∧ y < x := by
  obtain ⟨z, hlt⟩ := exists_lt (WithZero.unzero hx)
  rw [← WithZero.coe_lt_coe, WithZero.coe_unzero hx] at hlt
  exact ⟨z, WithZero.coe_ne_zero, hlt⟩

