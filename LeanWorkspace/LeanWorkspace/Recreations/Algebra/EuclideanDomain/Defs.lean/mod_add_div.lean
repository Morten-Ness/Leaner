import Mathlib

variable {R : Type u} [EuclideanDomain R]

theorem mod_add_div (a b : R) : a % b + b * (a / b) = a := (add_comm _ _).trans (EuclideanDomain.div_add_mod _ _)

