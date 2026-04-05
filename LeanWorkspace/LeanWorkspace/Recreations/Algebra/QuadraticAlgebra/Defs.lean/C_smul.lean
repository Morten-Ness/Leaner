import Mathlib

variable {R : Type*}

variable {S T : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)

theorem C_smul [Zero R] [SMulZeroClass S R] (s : S) (r : R) :
    (.C (s • r) : QuadraticAlgebra R a b) = s • .C r := QuadraticAlgebra.ext rfl (smul_zero _).symm

