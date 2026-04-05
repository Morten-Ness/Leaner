import Mathlib

variable {R : Type*}

variable {S T : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)

variable [Add R]

theorem mk_add_mk (z w : QuadraticAlgebra R a b) :
    QuadraticAlgebra.mk z.re z.im + QuadraticAlgebra.mk w.re w.im = (QuadraticAlgebra.mk (z.re + w.re) (z.im + w.im) : QuadraticAlgebra R a b) := rfl

