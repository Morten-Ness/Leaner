import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] [IsDomain R] {p q : R[X]}

theorem roots_C_mul (p : R[X]) (ha : a ≠ 0) : (C a * p).roots = p.roots := by
  by_cases hp : p = 0 <;>
    simp only [Polynomial.roots_mul, *, Ne, mul_eq_zero, C_eq_zero, or_self_iff, not_false_iff, Polynomial.roots_C,
      zero_add, mul_zero]

