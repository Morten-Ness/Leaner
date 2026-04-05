import Mathlib

section

open scoped Ring

variable {α : Type u}

theorem Invertible.ne_zero [MulZeroOneClass α] (a : α) [Nontrivial α] [Invertible a] : a ≠ 0 := fun ha =>
  zero_ne_one <|
    calc
      0 = ⅟a * a := by simp [ha]
      _ = 1 := invOf_mul_self

end

section

open scoped Ring

variable {α : Type u}

variable [MonoidWithZero α]

theorem Ring.inverse_invertible (x : α) [Invertible x] : x⁻¹ʳ = ⅟x := Ring.inverse_unit (unitOfInvertible _)

end

section

open scoped Ring

variable {α : Type u}

variable [GroupWithZero α]

theorem div_mul_cancel_of_invertible (a b : α) [Invertible b] : a / b * b = a := div_mul_cancel₀ a (Invertible.ne_zero b)

end

section

open scoped Ring

variable {α : Type u}

variable [GroupWithZero α]

theorem invOf_div (a b : α) [Invertible a] [Invertible b] [Invertible (a / b)] :
    ⅟(a / b) = b / a := invOf_eq_right_inv (by simp [← mul_div_assoc])

end

section

open scoped Ring

variable {α : Type u}

variable [GroupWithZero α]

theorem invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹ := invOf_eq_right_inv (mul_inv_cancel₀ (Invertible.ne_zero a))

end

section

open scoped Ring

variable {α : Type u}

variable [GroupWithZero α]

theorem inv_mul_cancel_of_invertible (a : α) [Invertible a] : a⁻¹ * a = 1 := inv_mul_cancel₀ (Invertible.ne_zero a)

end

section

open scoped Ring

variable {α : Type u}

variable [GroupWithZero α]

theorem mul_div_cancel_of_invertible (a b : α) [Invertible b] : a * b / b = a := mul_div_cancel_right₀ a (Invertible.ne_zero b)

end

section

open scoped Ring

variable {α : Type u}

variable [GroupWithZero α]

theorem mul_inv_cancel_of_invertible (a : α) [Invertible a] : a * a⁻¹ = 1 := mul_inv_cancel₀ (Invertible.ne_zero a)

end
