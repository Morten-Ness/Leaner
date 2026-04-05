import Mathlib

variable {α : Type*} [Semifield α] [LinearOrder α] [CanonicallyOrderedAdd α]

variable [IsStrictOrderedRing α] [Sub α] [OrderedSub α]

theorem tsub_div (a b c : α) : (a - b) / c = a / c - b / c := by simp_rw [div_eq_mul_inv, tsub_mul]

