import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

variable [Monoid M] [Monoid N]

theorem curryRingEquiv_symm_single (m : M) (n : N) (r : R) :
    MonoidAlgebra.curryRingEquiv.symm (single m <| single n r) = (single (m, n) r) := by
  classical exact Finsupp.uncurry_single ..

