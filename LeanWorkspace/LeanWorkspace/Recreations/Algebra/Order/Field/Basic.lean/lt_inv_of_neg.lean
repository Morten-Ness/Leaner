import Mathlib

variable {ι α β : Type*}

variable [Field α] [PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α]
  {a b c d : α} {n : ℤ}

theorem lt_inv_of_neg (ha : a < 0) (hb : b < 0) : a < b⁻¹ ↔ b < a⁻¹ := by
  simpa using inv_lt_inv_of_neg (inv_lt_zero'.2 ha) hb

