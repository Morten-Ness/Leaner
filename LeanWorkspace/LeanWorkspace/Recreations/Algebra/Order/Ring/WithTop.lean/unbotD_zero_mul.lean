import Mathlib

variable {α : Type*}

variable [DecidableEq α]

variable [MulZeroClass α] {a b : WithBot α}

theorem unbotD_zero_mul (a b : WithBot α) : (a * b).unbotD 0 = a.unbotD 0 * b.unbotD 0 := by
  by_cases ha : a = 0; · rw [ha, zero_mul, ← coe_zero, unbotD_coe, zero_mul]
  by_cases hb : b = 0; · rw [hb, mul_zero, ← coe_zero, unbotD_coe, mul_zero]
  cases a; · rw [bot_mul hb, unbotD_bot, zero_mul]
  cases b; · rw [mul_bot ha, unbotD_bot, mul_zero]
  rw [← coe_mul, unbotD_coe, unbotD_coe, unbotD_coe]

