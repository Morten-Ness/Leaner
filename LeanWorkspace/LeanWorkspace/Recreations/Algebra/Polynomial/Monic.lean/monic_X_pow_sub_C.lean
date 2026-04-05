import Mathlib

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Ring R] {p : R[X]}

theorem monic_X_pow_sub_C {R : Type u} [Ring R] (a : R) {n : ℕ} (h : n ≠ 0) :
    (Polynomial.X ^ n - Polynomial.C a).Monic := by
  simpa only [map_neg, ← sub_eq_add_neg] using Polynomial.monic_X_pow_add_C (-a) h

