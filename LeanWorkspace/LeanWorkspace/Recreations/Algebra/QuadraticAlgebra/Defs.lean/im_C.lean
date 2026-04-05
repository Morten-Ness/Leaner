import Mathlib

variable {R : Type*}

variable {S T : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)

variable [Zero R]

theorem im_C : (.C r : QuadraticAlgebra R a b).im = 0 := rfl

