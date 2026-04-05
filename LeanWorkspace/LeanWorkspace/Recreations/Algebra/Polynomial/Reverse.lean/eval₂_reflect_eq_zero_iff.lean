import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

variable {S : Type*} [CommSemiring S]

theorem eval₂_reflect_eq_zero_iff (i : R →+* S) (x : S) [Invertible x] (N : ℕ) (f : R[X])
    (hf : f.natDegree ≤ N) : eval₂ i (⅟x) (Polynomial.reflect N f) = 0 ↔ eval₂ i x f = 0 := by
  conv_rhs => rw [← Polynomial.eval₂_reflect_mul_pow i x N f hf]
  constructor
  · intro h
    rw [h, zero_mul]
  · intro h
    rw [← mul_one (eval₂ i (⅟x) _), ← one_pow N, ← mul_invOf_self x, mul_pow, ← mul_assoc, h,
      zero_mul]

