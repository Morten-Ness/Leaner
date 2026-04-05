import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

theorem coeff_finsuppSum [AddCommMonoid N] (f : ι →₀ N) (g : ι → N → R[M]) :
    MonoidAlgebra.coeff (f.sum g) = f.sum (fun i n ↦ MonoidAlgebra.coeff (g i n)) := map_finsuppSum MonoidAlgebra.coeffAddEquiv ..

