import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

theorem coeff_sum (s : Finset ι) (f : ι → R[M]) :
    MonoidAlgebra.coeff (∑ i ∈ s, f i) = ∑ i ∈ s, MonoidAlgebra.coeff (f i) := map_sum MonoidAlgebra.coeffAddEquiv ..

