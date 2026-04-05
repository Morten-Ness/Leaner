import Mathlib

variable {R : Type*}

variable {S T : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)

variable [Zero R]

variable [One R]

theorem C_one : (.C 1 : QuadraticAlgebra R a b) = 1 := rfl

