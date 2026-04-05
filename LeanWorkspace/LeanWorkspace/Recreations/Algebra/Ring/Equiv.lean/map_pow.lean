import Mathlib

variable {F α β R S S' : Type*}

variable [Semiring R] [Semiring S]

theorem map_pow (f : R ≃+* S) (a) : ∀ n : ℕ, f (a ^ n) = f a ^ n := map_pow f a

