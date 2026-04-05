import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

theorem ofCoeff_inj {x y : M →₀ R} : MonoidAlgebra.ofCoeff x = MonoidAlgebra.ofCoeff y ↔ x = y := MonoidAlgebra.ofCoeff_injective.eq_iff

