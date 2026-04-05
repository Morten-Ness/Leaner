import Mathlib

variable {R : Type*}

variable {S T : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)

variable (a b) [Semiring R]

theorem basis_repr_apply (x : QuadraticAlgebra R a b) :
    (QuadraticAlgebra.basis a b).repr x = ![x.re, x.im] := rfl

