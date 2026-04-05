import Mathlib

variable {R : Type*}

variable [Semiring R]

variable [Nontrivial R]

theorem isMonicOfDegree_X_add_one (r : R) : IsMonicOfDegree (X + C r) 1 := (Polynomial.isMonicOfDegree_X R).add_right (by rw [natDegree_C]; exact zero_lt_one)

