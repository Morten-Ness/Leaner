import Mathlib

variable (M N : Type*) [Monoid M] [Monoid N]

variable (R : Type v) [Semiring R]

theorem RingHom.smul_def (f : R →+* R) (a : R) : f • a = f a := rfl

