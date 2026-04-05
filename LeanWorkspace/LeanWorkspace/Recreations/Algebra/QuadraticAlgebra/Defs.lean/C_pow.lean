import Mathlib

variable {R : Type*}

variable {S T : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)

variable [CommSemiring R]

theorem C_pow (n : ℕ) (r : R) : (.C (r ^ n : R) : QuadraticAlgebra R a b) = (.C r) ^ n := (algebraMap R (QuadraticAlgebra R a b)).map_pow r n

