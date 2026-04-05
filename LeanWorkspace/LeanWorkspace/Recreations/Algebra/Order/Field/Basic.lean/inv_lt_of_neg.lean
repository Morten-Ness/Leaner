import Mathlib

variable {ι α β : Type*}

variable [Field α] [PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α]
  {a b c d : α} {n : ℤ}

theorem inv_lt_of_neg (ha : a < 0) (hb : b < 0) : a⁻¹ < b ↔ b⁻¹ < a := by
  simpa using inv_lt_inv_of_neg ha (inv_lt_zero'.2 hb)

