import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Ring R] {p q : R[X]}

theorem exists_eq_pow_rootMultiplicity_mul_and_not_dvd (p : R[X]) (hp : p ≠ 0) (a : R) :
    ∃ q : R[X], p = (Polynomial.X - Polynomial.C a) ^ p.rootMultiplicity a * q ∧ ¬ (Polynomial.X - Polynomial.C a) ∣ q := by
  classical
  rw [Polynomial.rootMultiplicity_eq_multiplicity, if_neg hp]
  apply (Polynomial.finiteMultiplicity_X_sub_C a hp).exists_eq_pow_mul_and_not_dvd

