import Mathlib

variable {R : Type*}

variable [Ring R]

variable [Nontrivial R]

theorem isMonicOfDegree_X_sub_one (r : R) : IsMonicOfDegree (X - C r) 1 := (Polynomial.isMonicOfDegree_X R).sub (by rw [natDegree_C]; exact zero_lt_one)

