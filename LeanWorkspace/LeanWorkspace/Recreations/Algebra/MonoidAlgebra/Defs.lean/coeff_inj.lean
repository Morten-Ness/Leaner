import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

theorem coeff_inj : x.coeff = y.coeff ↔ x = y := MonoidAlgebra.coeff_injective.eq_iff

