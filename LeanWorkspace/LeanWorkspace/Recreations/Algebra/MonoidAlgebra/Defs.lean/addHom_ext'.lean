import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

theorem addHom_ext' {N : Type*} [AddZeroClass N] ⦃f g : R[M] →+ N⦄
    (hfg : ∀ m, f.comp (MonoidAlgebra.singleAddHom m) = g.comp (MonoidAlgebra.singleAddHom m)) : f = g := Finsupp.addHom_ext' hfg

