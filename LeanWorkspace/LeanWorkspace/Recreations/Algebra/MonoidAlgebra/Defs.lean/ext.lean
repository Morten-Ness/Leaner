import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

set_option backward.inferInstanceAs.wrap false in
theorem ext ⦃f g : R[M]⦄ (hfg : ∀ m, f m = g m) : f = g := Finsupp.ext hfg

