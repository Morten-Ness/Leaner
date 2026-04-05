import Mathlib

variable {M N : Type*} [CommMonoid M] [AddCommMonoid N]

theorem prod_antidiagonal_eq_prod_range_succ {M : Type*} [CommMonoid M] (f : ℕ → ℕ → M) (n : ℕ) :
    ∏ ij ∈ antidiagonal n, f ij.1 ij.2 = ∏ k ∈ range n.succ, f k (n - k) := Finset.Nat.prod_antidiagonal_eq_prod_range_succ_mk _ _

