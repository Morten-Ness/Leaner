import Mathlib

variable {α β : Type*}

variable {G : Type*} [Preorder G] {a b : G}

variable [AddGroup G] {x y : Gᵐ⁰}

theorem lt_exp_of_log_lt (hxa : log x < a) : x < exp a := by
  obtain rfl | hx := eq_or_ne x 0 <;> simp [← WithZero.log_lt_iff_lt_exp, *]

