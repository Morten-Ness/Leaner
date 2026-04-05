import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [CommSemiring R]

theorem pow_sub_dvd_iterate_derivative_pow (p : R[X]) (n m : ℕ) :
    p ^ (n - m) ∣ Polynomial.derivative^[m] (p ^ n) := Polynomial.pow_sub_dvd_iterate_derivative_of_pow_dvd m dvd_rfl

