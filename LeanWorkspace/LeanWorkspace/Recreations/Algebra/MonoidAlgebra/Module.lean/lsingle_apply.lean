import Mathlib

variable (k : Type u₁) (G : Type u₂) (H : Type*) {R S M : Type*}

variable [Semiring k]

theorem lsingle_apply [Semiring R] [Module R k] (a : G) (b : k) :
    lsingle (R := R) a b = single a b :=
  rfl

