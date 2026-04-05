import Mathlib

variable {α : Type*}

variable [Ring α]

theorem iff_eq_of_mul_right_eq_one :
    IsDedekindFiniteMonoid α ↔ ∀ x y z : α, x * z = 1 → y * z = 1 → x = y := by
  refine (isDedekindFiniteMonoid_iff _).trans ⟨fun h x y z hxz hyz ↦ ?_, fun h x y eq ↦ ?_⟩
  · simpa [mul_assoc, h hyz] using congr_arg (· * y) hxz
  have := h _ (1 - y * x + x) _ eq <| by
    rw [add_mul, sub_mul, mul_assoc, eq, one_mul, mul_one, sub_self, zero_add]
  rwa [right_eq_add, sub_eq_zero, eq_comm] at this

