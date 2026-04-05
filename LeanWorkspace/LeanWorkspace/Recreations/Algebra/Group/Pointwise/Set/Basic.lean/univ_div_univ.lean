import Mathlib

variable {F α β γ : Type*}

variable [DivisionMonoid α] {s t : Set α} {n : ℤ}

theorem univ_div_univ : (univ / univ : Set α) = univ := by simp [div_eq_mul_inv]

