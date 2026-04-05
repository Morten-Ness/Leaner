import Mathlib

variable {R : Type*}

variable {S T : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)

theorem mk_sub_mk [Sub R] (x1 y1 x2 y2 : R) :
    (QuadraticAlgebra.mk x1 y1 : QuadraticAlgebra R a b) - QuadraticAlgebra.mk x2 y2 = QuadraticAlgebra.mk (x1 - x2) (y1 - y2) := rfl

