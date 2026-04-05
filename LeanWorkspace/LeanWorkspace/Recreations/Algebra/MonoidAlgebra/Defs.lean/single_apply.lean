import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

theorem single_apply {a a' : M} {b : R} [Decidable (a = a')] :
    single a b a' = if a = a' then b else 0 := Finsupp.single_apply

