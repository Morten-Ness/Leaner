import Mathlib

variable {α : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a : α}

theorem inv_Iio₀ {a : α} (ha : a < 0) : (Iio a)⁻¹ = Ioo a⁻¹ 0 := by
  rw [inv_eq_iff_eq_inv, Set.inv_Ioo_0_right (inv_neg''.2 ha), inv_inv]

