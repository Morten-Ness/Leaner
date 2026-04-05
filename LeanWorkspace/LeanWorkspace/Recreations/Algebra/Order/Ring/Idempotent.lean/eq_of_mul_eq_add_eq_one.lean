import Mathlib

variable {R : Type*}

theorem eq_of_mul_eq_add_eq_one [NonAssocSemiring R] (a : R) {b c : R}
    (mul : a * b = c * a) (add_ab : a + b = 1) (add_ac : a + c = 1) :
    b = c := calc b = (a + c) * b := by rw [add_ac, one_mul]
       _ = c * (a + b) := by rw [add_mul, mul, mul_add]
       _ = c := by rw [add_ab, mul_one]

