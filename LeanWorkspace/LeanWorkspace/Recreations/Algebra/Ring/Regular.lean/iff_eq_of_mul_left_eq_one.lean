import Mathlib

variable {α : Type*}

variable [Ring α]

theorem iff_eq_of_mul_left_eq_one :
    IsDedekindFiniteMonoid α ↔ ∀ x y z : α, x * y = 1 → x * z = 1 → y = z := by
  refine (isDedekindFiniteMonoid_iff _).trans ⟨fun h x y z hxy hxz ↦ ?_, fun h x y eq ↦ ?_⟩
  · simpa [← mul_assoc, h hxz] using congr_arg (z * ·) hxy
  have := h _ _ (1 - y * x + y) eq <| by
    rw [mul_add, mul_sub, ← mul_assoc, eq, mul_one, one_mul, sub_self, zero_add]
  rwa [right_eq_add, sub_eq_zero, eq_comm] at this

