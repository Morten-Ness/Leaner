import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

theorem ofCoeff_erase (m : M) (x : M →₀ R) : MonoidAlgebra.ofCoeff (x.erase m) = (MonoidAlgebra.ofCoeff x).erase m := rfl

