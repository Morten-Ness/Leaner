import Mathlib

variable {α : Type u}

variable {M : Type*} {N : Type*}

variable [DivisionMonoid α] {a b c : α}

theorem div (ha : IsUnit a) (hb : IsUnit b) : IsUnit (a / b) := by
  rw [div_eq_mul_inv]; exact ha.mul IsUnit.inv hb

