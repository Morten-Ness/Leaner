import Mathlib

variable {R : Type*}

variable {S T : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)

variable [AddCommMonoidWithOne R]

theorem re_natCast (n : ℕ) : (n : QuadraticAlgebra R a b).re = n := rfl

