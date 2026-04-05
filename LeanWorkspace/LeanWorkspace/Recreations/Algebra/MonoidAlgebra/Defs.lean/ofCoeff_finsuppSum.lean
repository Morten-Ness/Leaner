import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

theorem ofCoeff_finsuppSum [AddCommMonoid N] (f : ι →₀ N) (g : ι → N → M →₀ R) :
    MonoidAlgebra.ofCoeff (f.sum g) = f.sum (fun i n ↦ MonoidAlgebra.ofCoeff (g i n)) := map_finsuppSum MonoidAlgebra.coeffAddEquiv.symm ..

-- TODO: This definition is very leaky, and we later have frequent problems conflating the two
-- versions of `single`. Perhaps someone wants to try making this a `def` rather than an `abbrev`?
-- In Mathlib 3 this was locally reducible.

