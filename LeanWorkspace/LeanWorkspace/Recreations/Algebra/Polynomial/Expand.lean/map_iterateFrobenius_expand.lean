import Mathlib

open scoped Polynomial

variable (R : Type u) [CommSemiring R] {S : Type v} [CommSemiring S] (p q : ℕ)

variable [ExpChar R p]

theorem map_iterateFrobenius_expand (f : R[X]) (n : ℕ) :
    map (iterateFrobenius R p n) (Polynomial.expand R (p ^ n) f) = f ^ p ^ n := by
  induction n with
  | zero => simp
  | succ k n_ih =>
    symm
    conv_lhs => rw [pow_succ, pow_mul, ← n_ih]
    simp_rw [← Polynomial.map_frobenius_expand p, pow_succ', add_comm k, iterateFrobenius_add,
      ← map_map, ← Polynomial.map_expand, ← Polynomial.expand_mul, iterateFrobenius_one]

