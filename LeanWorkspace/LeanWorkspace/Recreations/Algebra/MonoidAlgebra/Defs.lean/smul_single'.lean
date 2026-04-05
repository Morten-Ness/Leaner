import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

variable {A : Type*} [SMulZeroClass A R]

theorem smul_single' (r' : R) (m : M) (r : R) : r' • single m r = single m (r' * r) := MonoidAlgebra.smul_single ..

