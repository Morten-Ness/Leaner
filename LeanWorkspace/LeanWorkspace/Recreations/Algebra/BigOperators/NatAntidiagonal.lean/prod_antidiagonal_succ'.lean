import Mathlib

variable {M N : Type*} [CommMonoid M] [AddCommMonoid N]

theorem prod_antidiagonal_succ' {n : ℕ} {f : ℕ × ℕ → M} : (∏ p ∈ antidiagonal (n + 1), f p) =
    f (n + 1, 0) * ∏ p ∈ antidiagonal n, f (p.1, p.2 + 1) := by
  rw [← Finset.Nat.prod_antidiagonal_swap, Finset.Nat.prod_antidiagonal_succ, ← Finset.Nat.prod_antidiagonal_swap]
  rfl

