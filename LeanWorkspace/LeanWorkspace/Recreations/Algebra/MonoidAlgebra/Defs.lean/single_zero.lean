import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

theorem single_zero (m : M) : (single m 0 : R[M]) = 0 := Finsupp.single_zero m

