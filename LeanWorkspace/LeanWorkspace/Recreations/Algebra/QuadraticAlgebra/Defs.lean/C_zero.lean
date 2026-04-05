import Mathlib

variable {R : Type*}

variable {S T : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)

variable [Zero R]

theorem C_zero : (.C 0 : QuadraticAlgebra R a b) = 0 := rfl

