import Mathlib

variable {F α β : Type*}

theorem IsSquare.div [DivisionCommMonoid α] {a b : α} (ha : IsSquare a) (hb : IsSquare b) :
    IsSquare (a / b) := by aesop (add simp div_eq_mul_inv)

