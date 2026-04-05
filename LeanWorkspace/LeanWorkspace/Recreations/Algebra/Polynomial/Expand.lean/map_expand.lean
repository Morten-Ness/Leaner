import Mathlib

open scoped Polynomial

variable (R : Type u) [CommSemiring R] {S : Type v} [CommSemiring S] (p q : ℕ)

theorem map_expand {p : ℕ} {f : R →+* S} {q : R[X]} :
    map f (Polynomial.expand R p q) = Polynomial.expand S p (map f q) := by
  by_cases hp : p = 0
  · simp [hp]
  ext
  rw [coeff_map, Polynomial.coeff_expand (Nat.pos_of_ne_zero hp), Polynomial.coeff_expand (Nat.pos_of_ne_zero hp)]
  split_ifs <;> simp_all

