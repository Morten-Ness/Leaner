import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

variable {A : Type*} [SMulZeroClass A R]

theorem smul_apply (a : A) (x : R[M]) (m : M) : (a • x) m = a • x m := rfl

