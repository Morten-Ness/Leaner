import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

variable {A : Type*} [SMulZeroClass A R]

theorem smul_single (a : A) (m : M) (r : R) : a • single m r = single m (a • r) := by
  ext
  simp [single, ← Finsupp.smul_single]

