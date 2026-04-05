import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

theorem single_add (m : M) (r₁ r₂ : R) : single m (r₁ + r₂) = single m r₁ + single m r₂ := Finsupp.single_add m r₁ r₂

