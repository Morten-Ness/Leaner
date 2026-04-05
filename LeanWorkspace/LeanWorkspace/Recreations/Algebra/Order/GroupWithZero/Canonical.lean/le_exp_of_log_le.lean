import Mathlib

variable {α β : Type*}

variable {G : Type*} [Preorder G] {a b : G}

variable [AddGroup G] {x y : Gᵐ⁰}

theorem le_exp_of_log_le (hxa : log x ≤ a) : x ≤ exp a := by
  obtain rfl | hx := eq_or_ne x 0 <;> simp [← WithZero.log_le_iff_le_exp, *]

