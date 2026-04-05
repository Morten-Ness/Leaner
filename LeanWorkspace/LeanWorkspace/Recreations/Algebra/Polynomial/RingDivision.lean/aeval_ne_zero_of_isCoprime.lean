import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R]

variable [IsDomain R] {p q : R[X]}

theorem aeval_ne_zero_of_isCoprime {R} [CommSemiring R] [Nontrivial S] [Semiring S] [Algebra R S]
    {p q : R[X]} (h : IsCoprime p q) (s : S) : Polynomial.aeval s p ≠ 0 ∨ Polynomial.aeval s q ≠ 0 := by
  by_contra! ⟨hp, hq⟩
  rcases h with ⟨_, _, h⟩
  apply_fun Polynomial.aeval s at h
  simp only [map_add, map_mul, map_one, hp, hq, mul_zero, add_zero, zero_ne_one] at h

