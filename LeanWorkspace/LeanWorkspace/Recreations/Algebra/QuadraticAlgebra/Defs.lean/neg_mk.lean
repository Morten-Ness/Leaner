import Mathlib

variable {R : Type*}

variable {S T : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)

variable [Neg R]

theorem neg_mk (x y : R) :
    -(QuadraticAlgebra.mk x y : QuadraticAlgebra R a b) = ⟨-x, -y⟩ := rfl

