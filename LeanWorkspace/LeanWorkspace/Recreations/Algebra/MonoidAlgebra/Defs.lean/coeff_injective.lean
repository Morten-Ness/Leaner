import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

theorem coeff_injective : (MonoidAlgebra.coeff : R[M] → M →₀ R).Injective := MonoidAlgebra.coeffEquiv.injective

