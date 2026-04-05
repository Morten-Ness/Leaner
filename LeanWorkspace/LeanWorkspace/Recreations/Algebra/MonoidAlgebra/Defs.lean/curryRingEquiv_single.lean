import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

variable [Monoid M] [Monoid N]

theorem curryRingEquiv_single (m : M) (n : N) (r : R) :
    MonoidAlgebra.curryRingEquiv (single (m, n) r) = single m (single n r) := by
  classical exact Finsupp.curry_single ..

