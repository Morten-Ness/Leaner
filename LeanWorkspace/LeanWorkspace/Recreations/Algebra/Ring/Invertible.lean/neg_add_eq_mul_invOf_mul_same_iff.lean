import Mathlib

open scoped Ring

variable {R : Type*}

theorem neg_add_eq_mul_invOf_mul_same_iff [Ring R] {a b : R} [Invertible a] [Invertible b] :
    -(b + a) = a * ⅟b * a ↔ -1 = ⅟a * b + ⅟b * a := calc -(b + a) = a * ⅟b * a
      ↔ -a = b + a * ⅟b * a := ⟨by grind, fun h ↦ by simp [h]⟩
    _ ↔ -a = a * ⅟a * b + a * ⅟b * a := by rw [mul_invOf_self, one_mul]
    _ ↔ -a = a * (⅟a * b + ⅟b * a) := by simp only [mul_add, mul_assoc]
    _ ↔ -1 = ⅟a * b + ⅟b * a := ⟨fun h ↦ by simpa using congr_arg (⅟a * ·) h, fun h ↦ by simp [← h]⟩

