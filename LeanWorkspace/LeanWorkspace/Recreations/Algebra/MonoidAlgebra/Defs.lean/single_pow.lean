import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

variable [Monoid M] [Monoid N]

theorem single_pow (m : M) (r : R) : ∀ n : ℕ, single m r ^ n = single (m ^ n) (r ^ n)
  | 0 => by simp [MonoidAlgebra.one_def]
  | n + 1 => by simp [pow_succ, single_pow _ _ n]
