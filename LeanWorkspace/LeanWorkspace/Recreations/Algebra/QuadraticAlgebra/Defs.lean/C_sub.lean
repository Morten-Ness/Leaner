import Mathlib

variable {R : Type*}

variable {S T : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)

theorem C_sub (r1 r2 : R) [SubNegZeroMonoid R] :
    (.C (r1 - r2) : QuadraticAlgebra R a b) = .C r1 - .C r2 := QuadraticAlgebra.ext rfl zero_sub_zero.symm

