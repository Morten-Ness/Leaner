import Mathlib

variable {R : Type*}

theorem add_iff [NonUnitalNonAssocSemiring R] [IsCancelAdd R]
    {a b : R} (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) :
    IsIdempotentElem (a + b) ↔ a * b + b * a = 0 := by
  refine ⟨fun h ↦ ?_, IsIdempotentElem.add ha hb⟩
  rw [← add_right_cancel_iff (a := b), add_assoc, ← add_left_cancel_iff (a := a),
    ← add_assoc, add_add_add_comm]
  simpa [add_mul, mul_add, ha.eq, hb.eq] using h.eq

