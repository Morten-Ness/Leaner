import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

theorem ofCoeff_update (m : M) (r : R) (x : M →₀ R) :
    MonoidAlgebra.ofCoeff (x.update m r) = (MonoidAlgebra.ofCoeff x).update m r := rfl

