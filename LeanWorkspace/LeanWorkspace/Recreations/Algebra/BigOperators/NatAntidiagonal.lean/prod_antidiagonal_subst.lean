import Mathlib

variable {M N : Type*} [CommMonoid M] [AddCommMonoid N]

theorem prod_antidiagonal_subst {n : ℕ} {f : ℕ × ℕ → ℕ → M} :
    ∏ p ∈ antidiagonal n, f p n = ∏ p ∈ antidiagonal n, f p (p.1 + p.2) := prod_congr rfl fun p hp ↦ by rw [mem_antidiagonal.mp hp]

