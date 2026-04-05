import Mathlib

variable {R : Type*}

variable {S T : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)

variable (a b) [Semiring R]

theorem linearEquivTuple_apply (z : QuadraticAlgebra R a b) :
    (QuadraticAlgebra.linearEquivTuple a b) z = ![z.re, z.im] := rfl

