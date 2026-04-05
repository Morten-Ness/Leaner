import Mathlib

variable {M N : Type*} [CommMonoid M] [AddCommMonoid N]

theorem sum_antidiagonal_succ {n : ℕ} {f : ℕ × ℕ → N} :
    (∑ p ∈ antidiagonal (n + 1), f p) = f (0, n + 1) + ∑ p ∈ antidiagonal n, f (p.1 + 1, p.2) := @Finset.Nat.prod_antidiagonal_succ (Multiplicative N) _ _ _

