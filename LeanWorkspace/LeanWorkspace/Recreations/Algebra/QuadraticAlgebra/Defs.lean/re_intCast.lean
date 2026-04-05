import Mathlib

variable {R : Type*}

variable {S T : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)

variable [AddCommGroupWithOne R]

theorem re_intCast (n : ℤ) : (n : QuadraticAlgebra R a b).re = n := rfl

