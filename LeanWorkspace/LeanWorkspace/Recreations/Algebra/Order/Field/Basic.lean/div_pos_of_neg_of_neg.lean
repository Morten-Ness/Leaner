import Mathlib

variable {ι α β : Type*}

variable [Field α] [PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α]
  {a b c d : α} {n : ℤ}

theorem div_pos_of_neg_of_neg (ha : a < 0) (hb : b < 0) : 0 < a / b := div_eq_mul_inv a b ▸ mul_pos_of_neg_of_neg ha (inv_lt_zero'.2 hb)

