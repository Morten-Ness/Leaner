import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem lcm_eq_zero_iff [GCDMonoid α] (a b : α) : lcm a b = 0 ↔ a = 0 ∨ b = 0 := Iff.intro
    (fun h : lcm a b = 0 => by
      have : Associated (a * b) 0 := (gcd_mul_lcm a b).symm.trans <| by rw [h, mul_zero]
      rwa [← mul_eq_zero, ← associated_zero_iff_eq_zero])
    (by rintro (rfl | rfl) <;> [apply lcm_zero_left; apply lcm_zero_right])

