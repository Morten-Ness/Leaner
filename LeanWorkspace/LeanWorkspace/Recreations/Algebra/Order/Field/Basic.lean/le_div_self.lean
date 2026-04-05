import Mathlib

variable {ι α β : Type*}

variable [Semifield α] [PartialOrder α] [PosMulReflectLT α] {a b c d e : α} {m n : ℤ}

theorem le_div_self (ha : 0 ≤ a) (hb₀ : 0 < b) (hb₁ : b ≤ 1) : a ≤ a / b := by
  simpa only [div_one] using div_le_div_of_nonneg_left ha hb₀ hb₁

