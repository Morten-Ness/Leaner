import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [CommSemiring R] {p q : R[X]} {x : R} [CommSemiring S] (f : R →+* S)

theorem eval_eq_zero_of_dvd_of_eval_eq_zero : p ∣ q → Polynomial.eval x p = 0 → Polynomial.eval x q = 0 := Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero _ _

