import Mathlib

variable {R : Type*}

variable {S T : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)

variable [SMul S R] [SMul T R] (s : S)

theorem smul_mk (s : S) (x y : R) :
    s • (QuadraticAlgebra.mk x y : QuadraticAlgebra R a b) = QuadraticAlgebra.mk (s • x) (s • y) := rfl

