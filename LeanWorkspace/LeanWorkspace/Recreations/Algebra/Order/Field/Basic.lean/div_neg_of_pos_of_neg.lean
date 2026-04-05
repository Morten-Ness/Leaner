import Mathlib

variable {ι α β : Type*}

variable [Field α] [PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α]
  {a b c d : α} {n : ℤ}

theorem div_neg_of_pos_of_neg (ha : 0 < a) (hb : b < 0) : a / b < 0 := div_eq_mul_inv a b ▸ mul_neg_of_pos_of_neg ha (inv_lt_zero'.2 hb)

