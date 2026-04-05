import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

theorem coeff_update (m : M) (r : R) (x : R[M]) :
    (x.update m r).coeff = x.coeff.update m r := rfl

