import Mathlib

variable {K : Type*} [Field K]

theorem mod_eq (a b : K) : a % b = a - a * b / b := rfl

