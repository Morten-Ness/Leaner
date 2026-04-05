import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Ring R] {p q : R[X]}

theorem pow_rootMultiplicity_dvd (p : R[X]) (a : R) : (Polynomial.X - Polynomial.C a) ^ Polynomial.rootMultiplicity a p ∣ p := letI := Classical.decEq R
  if h : p = 0 then by simp [h]
  else by
    classical
    rw [Polynomial.rootMultiplicity_eq_multiplicity, if_neg h]; apply pow_multiplicity_dvd

