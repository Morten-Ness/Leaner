import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [DivisionMonoid α] {s t : Finset α} {n : ℤ}

theorem univ_div_univ [Fintype α] : (univ / univ : Finset α) = univ := by simp [div_eq_mul_inv]

