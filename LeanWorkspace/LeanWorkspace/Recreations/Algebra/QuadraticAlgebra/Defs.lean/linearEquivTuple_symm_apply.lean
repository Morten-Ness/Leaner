import Mathlib

variable {R : Type*}

variable {S T : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)

variable (a b) [Semiring R]

theorem linearEquivTuple_symm_apply (x : Fin 2 → R) :
    (QuadraticAlgebra.linearEquivTuple a b).symm x = ⟨x 0, x 1⟩ := rfl

