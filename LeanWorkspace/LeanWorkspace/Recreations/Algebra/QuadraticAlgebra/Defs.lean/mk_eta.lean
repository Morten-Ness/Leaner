import Mathlib

variable {R : Type*}

theorem mk_eta {a b} (z : QuadraticAlgebra R a b) :
    QuadraticAlgebra.mk z.re z.im = z := rfl

