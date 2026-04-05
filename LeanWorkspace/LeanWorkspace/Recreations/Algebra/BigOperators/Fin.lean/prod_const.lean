import Mathlib

variable {ι M : Type*}

variable [CommMonoid M] {n : ℕ}

theorem prod_const (n : ℕ) (x : M) : ∏ _i : Fin n, x = x ^ n := by simp

