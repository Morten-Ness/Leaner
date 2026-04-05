import Mathlib

open scoped Polynomial

variable (R : Type u) [CommSemiring R] {S : Type v} [CommSemiring S] (p q : ℕ)

theorem expand_one (f : R[X]) : Polynomial.expand R 1 f = f := Polynomial.induction_on f (fun r => by rw [Polynomial.expand_C])
    (fun f g ihf ihg => by rw [map_add, ihf, ihg]) fun n r _ => by
    rw [map_mul, Polynomial.expand_C, map_pow, Polynomial.expand_X, pow_one]

