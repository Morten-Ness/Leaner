import Mathlib

variable {α β G M : Type*}

variable [CommGroup G] {a b c d : G}

theorem div_eq_of_eq_mul' {a b c : G} (h : a = b * c) : a / b = c := by
  rw [h, div_eq_mul_inv, mul_comm, inv_mul_cancel_left]

