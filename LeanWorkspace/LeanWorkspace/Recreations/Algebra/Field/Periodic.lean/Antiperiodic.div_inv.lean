import Mathlib

variable {α β γ : Type*} {f g : α → β} {c c₁ c₂ x : α}

theorem Antiperiodic.div_inv [DivisionSemiring α] [Neg β] (h : Antiperiodic f c) {a : α}
    (ha : a ≠ 0) : Antiperiodic (fun x => f (x / a)) (c * a) := by
  simpa only [div_eq_mul_inv] using h.mul_const_inv ha

