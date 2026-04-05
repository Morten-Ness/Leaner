import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

theorem ofCoeff_injective : (MonoidAlgebra.ofCoeff : (M →₀ R) → R[M]).Injective := MonoidAlgebra.coeffEquiv.symm.injective

