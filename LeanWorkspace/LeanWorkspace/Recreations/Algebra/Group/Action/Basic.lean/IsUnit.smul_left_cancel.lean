import Mathlib

variable {G M A B α β : Type*}

variable [Monoid α] [MulAction α β]

theorem smul_left_cancel {a : α} (ha : IsUnit a) {x y : β} : a • x = a • y ↔ x = y := let ⟨u, hu⟩ := ha
  hu ▸ smul_left_cancel_iff u

