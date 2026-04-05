import Mathlib

variable {ι α β : Type*}

variable [Semifield α] [PartialOrder α] [PosMulReflectLT α] {a b c d e : α} {m n : ℤ}

variable [IsStrictOrderedRing α]

theorem inv_pow_lt_inv_pow_of_lt (a1 : 1 < a) {m n : ℕ} (mn : m < n) : (a ^ n)⁻¹ < (a ^ m)⁻¹ := by
  convert one_div_pow_lt_one_div_pow_of_lt a1 mn using 1 <;> simp

