import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

theorem mod_eq_sub_mul_div {R : Type*} [EuclideanDomain R] (a b : R) : a % b = a - b * (a / b) := calc
    a % b = b * (a / b) + a % b - b * (a / b) := (add_sub_cancel_left _ _).symm
    _ = a - b * (a / b) := by rw [div_add_mod]

