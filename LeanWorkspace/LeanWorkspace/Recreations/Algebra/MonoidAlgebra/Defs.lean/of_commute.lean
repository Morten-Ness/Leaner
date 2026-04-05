import Mathlib

variable {R S G M N O ι : Type*}

variable [Semiring R] {x y : R[M]} {r r₁ r₂ : R} {m m' m₁ m₂ : M}

variable [MulOneClass M]

theorem of_commute (h : ∀ m', Commute m m') (f : R[M]) : Commute (MonoidAlgebra.of R M m) f := MonoidAlgebra.single_commute h .one_left f

