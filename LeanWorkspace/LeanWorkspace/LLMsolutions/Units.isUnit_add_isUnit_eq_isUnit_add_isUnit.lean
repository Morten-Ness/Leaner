import Mathlib

variable {u v : ℤ}

theorem isUnit_add_isUnit_eq_isUnit_add_isUnit {a b c d : ℤ} (ha : IsUnit a) (hb : IsUnit b)
    (hc : IsUnit c) (hd : IsUnit d) : a + b = c + d ↔ a = c ∧ b = d ∨ a = d ∧ b = c := by
  rcases Int.isUnit_iff.mp ha with rfl | rfl <;>
    rcases Int.isUnit_iff.mp hb with rfl | rfl <;>
    rcases Int.isUnit_iff.mp hc with rfl | rfl <;>
    rcases Int.isUnit_iff.mp hd with rfl | rfl <;>
    decide
