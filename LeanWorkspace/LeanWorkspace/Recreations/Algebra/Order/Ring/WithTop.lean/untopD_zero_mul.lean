import Mathlib

variable {α : Type*}

variable [DecidableEq α]

variable [MulZeroClass α] {a b : WithTop α}

theorem untopD_zero_mul (a b : WithTop α) : (a * b).untopD 0 = a.untopD 0 * b.untopD 0 := by
  by_cases ha : a = 0; · rw [ha, zero_mul, ← coe_zero, untopD_coe, zero_mul]
  by_cases hb : b = 0; · rw [hb, mul_zero, ← coe_zero, untopD_coe, mul_zero]
  cases a; · rw [top_mul hb, untopD_top, zero_mul]
  cases b; · rw [mul_top ha, untopD_top, mul_zero]
  rw [← coe_mul, untopD_coe, untopD_coe, untopD_coe]

