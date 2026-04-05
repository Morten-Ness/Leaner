import Mathlib

variable {M N : Type*} [CommMonoid M] [AddCommMonoid N]

theorem sum_antidiagonal_succ' {n : ℕ} {f : ℕ × ℕ → N} :
    (∑ p ∈ antidiagonal (n + 1), f p) = f (n + 1, 0) + ∑ p ∈ antidiagonal n, f (p.1, p.2 + 1) := @Finset.Nat.prod_antidiagonal_succ' (Multiplicative N) _ _ _

