import Mathlib

variable {α β : Type*}

variable [LinearOrder α] {a b c : α} {x y : WithZero α}

theorem exists_ne_zero_and_le_and_le (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ z, z ≠ 0 ∧ z ≤ x ∧ z ≤ y := ⟨x ⊓ y, by simp [min_eq_iff, hx, hy], by simp, by simp⟩

