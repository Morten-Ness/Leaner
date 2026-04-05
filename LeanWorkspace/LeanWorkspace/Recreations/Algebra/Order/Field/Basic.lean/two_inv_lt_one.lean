import Mathlib

variable {ι α β : Type*}

variable [Semifield α] [PartialOrder α] [PosMulReflectLT α] {a b c d e : α} {m n : ℤ}

variable [IsStrictOrderedRing α]

theorem two_inv_lt_one : (2⁻¹ : α) < 1 := (one_div _).symm.trans_lt one_half_lt_one

