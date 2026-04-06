FAIL
import Mathlib

variable {M : Type*} {S T : Set M}

variable [Monoid M]

theorem invOf_mem_center {a : M} [Invertible a] (ha : a ∈ Set.center M) : ⅟a ∈ Set.center M := by
  rw [Set.mem_center_iff] at ha ⊢
  exact fun b => by
    calc
      b * ⅟ a = ⅟ a * (a * (b * ⅟ a)) := by
        rw [← mul_assoc, invOf_mul_self, one_mul]
      _ = ⅟ a * ((a * b) * ⅟ a) := by rw [mul_assoc]
      _ = ⅟ a * ((b * a) * ⅟ a) := by rw [ha b]
      _ = ⅟ a * (b * (a * ⅟ a)) := by rw [← mul_assoc]
      _ = ⅟ a * (b * 1) := by rw [mul_invOf_self]
      _ = ⅟ a * b := by rw [mul_one]
