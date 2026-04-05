import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

theorem ofCoeff_sum (s : Finset ι) (f : ι → M →₀ R) :
    MonoidAlgebra.ofCoeff (∑ i ∈ s, f i) = ∑ i ∈ s, MonoidAlgebra.ofCoeff (f i) := map_sum MonoidAlgebra.coeffAddEquiv.symm ..

