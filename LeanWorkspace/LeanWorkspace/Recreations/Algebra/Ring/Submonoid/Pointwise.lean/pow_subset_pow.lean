import Mathlib

open scoped Pointwise

variable {M R A : Type*}

variable [Semiring R]

theorem pow_subset_pow {s : AddSubmonoid R} {n : ℕ} : (↑s : Set R) ^ n ⊆ ↑(s ^ n) := (AddSubmonoid.pow_eq_closure_pow_set s n).symm ▸ subset_closure

