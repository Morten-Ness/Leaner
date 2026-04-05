import Mathlib

variable {R : Type*}

variable {S T : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)

variable [AddCommGroupWithOne R]

theorem C_intCast (n : ℤ) : .C (n : R) = (n : QuadraticAlgebra R a b) := rfl

