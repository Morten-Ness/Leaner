import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Ring R] {p q : R[X]}

theorem pow_mul_divByMonic_rootMultiplicity_eq (p : R[X]) (a : R) :
    (Polynomial.X - Polynomial.C a) ^ Polynomial.rootMultiplicity a p * (p /ₘ (Polynomial.X - Polynomial.C a) ^ Polynomial.rootMultiplicity a p) = p := by
  have : Polynomial.Monic ((Polynomial.X - Polynomial.C a) ^ Polynomial.rootMultiplicity a p) := (Polynomial.monic_X_sub_C _).pow _
  conv_rhs =>
    rw [← Polynomial.modByMonic_add_div p, (Polynomial.modByMonic_eq_zero_iff_dvd this).2 (Polynomial.pow_rootMultiplicity_dvd _ _)]
  simp

