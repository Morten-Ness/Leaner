import Mathlib

variable {R : Type*}

variable {S T : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)

variable [Mul R] [Add R]

theorem mk_mul_mk (x1 y1 x2 y2 : R) :
    (QuadraticAlgebra.mk x1 y1 : QuadraticAlgebra R a b) * QuadraticAlgebra.mk x2 y2 =
    QuadraticAlgebra.mk (x1 * x2 + a * y1 * y2) (x1 * y2 + y1 * x2 + b * y1 * y2) := rfl

