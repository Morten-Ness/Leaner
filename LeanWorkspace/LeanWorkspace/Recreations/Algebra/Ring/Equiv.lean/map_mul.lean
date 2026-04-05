import Mathlib

variable {F α β R S S' : Type*}

variable [Mul R] [Mul S] [Add R] [Add S] [Mul S'] [Add S']

theorem map_mul (e : R ≃+* S) (x y : R) : e (x * y) = e x * e y := map_mul e x y

