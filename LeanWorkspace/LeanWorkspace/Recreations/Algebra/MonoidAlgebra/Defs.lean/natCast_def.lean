import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

variable [MulOneClass M]

theorem natCast_def (n : ℕ) : (n : R[M]) = single (1 : M) (n : R) := rfl

