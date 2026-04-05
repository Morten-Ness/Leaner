import Mathlib

open scoped Polynomial

variable (R : Type u) [CommSemiring R] {S : Type v} [CommSemiring S] (p q : ℕ)

theorem expand_expand (f : R[X]) : Polynomial.expand R p (Polynomial.expand R q f) = Polynomial.expand R (p * q) f := Polynomial.induction_on f (fun r => by simp_rw [Polynomial.expand_C])
    (fun f g ihf ihg => by simp_rw [map_add, ihf, ihg]) fun n r _ => by
    simp_rw [map_mul, Polynomial.expand_C, map_pow, Polynomial.expand_X, map_pow, Polynomial.expand_X, pow_mul]

