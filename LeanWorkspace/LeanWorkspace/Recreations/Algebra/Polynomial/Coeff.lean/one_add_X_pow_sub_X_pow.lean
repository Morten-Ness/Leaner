import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem one_add_X_pow_sub_X_pow {S : Type*} [CommRing S] (d : ℕ) :
    (1 + Polynomial.X : S[X]) ^ d - Polynomial.X ^ d = ∑ i ∈ range d, d.choose i • Polynomial.X ^ i := by
  ext i
  simp [Polynomial.coeff_one_add_X_pow]
  split_ifs <;> simp_all [Nat.choose_eq_zero_of_lt, lt_iff_le_and_ne]

