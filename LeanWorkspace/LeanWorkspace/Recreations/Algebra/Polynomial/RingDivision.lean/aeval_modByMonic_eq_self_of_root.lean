import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R] {p q : R[X]}

variable [Ring S]

theorem aeval_modByMonic_eq_self_of_root [Algebra R S] {p q : R[X]} {x : S}
    (hx : Polynomial.aeval x q = 0) : Polynomial.aeval x (p %ₘ q) = Polynomial.aeval x p := by
  --`eval₂_modByMonic_eq_self_of_root` doesn't work here as it needs commutativity
  rw [modByMonic_eq_sub_mul_div, map_sub, map_mul, hx, zero_mul, sub_zero]

