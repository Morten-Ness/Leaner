import Mathlib

variable {R : Type*}

variable {S T : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)

variable [Zero R]

theorem re_C : (.C r : QuadraticAlgebra R a b).re = r := rfl

