import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

theorem ofCoeff_add (x y : M →₀ R) : MonoidAlgebra.ofCoeff (x + y) = MonoidAlgebra.ofCoeff x + MonoidAlgebra.ofCoeff y := rfl

