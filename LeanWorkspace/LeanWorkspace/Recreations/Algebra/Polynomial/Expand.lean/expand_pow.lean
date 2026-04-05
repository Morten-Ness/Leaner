import Mathlib

open scoped Polynomial

variable (R : Type u) [CommSemiring R] {S : Type v} [CommSemiring S] (p q : ℕ)

theorem expand_pow (f : R[X]) : Polynomial.expand R (p ^ q) f = (Polynomial.expand R p)^[q] f := Nat.recOn q (by rw [pow_zero, Polynomial.expand_one, Function.iterate_zero, id]) fun n ih => by
    rw [Function.iterate_succ_apply', pow_succ', Polynomial.expand_mul, ih]

