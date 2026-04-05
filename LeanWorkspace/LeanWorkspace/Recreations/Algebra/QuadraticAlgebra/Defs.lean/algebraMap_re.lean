import Mathlib

variable {R : Type*}

variable {S T : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)

variable [CommSemiring R]

theorem algebraMap_re : (algebraMap R (QuadraticAlgebra R a b) r).re = r := rfl

