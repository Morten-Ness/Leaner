import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [CommSemiring R]

theorem pow_sub_dvd_iterate_derivative_of_pow_dvd {p q : R[X]} {n : ℕ} (m : ℕ)
    (dvd : q ^ n ∣ p) : q ^ (n - m) ∣ Polynomial.derivative^[m] p := by
  induction m generalizing p with
  | zero => simpa
  | succ m ih =>
    rw [Nat.sub_succ, Function.iterate_succ']
    exact Polynomial.pow_sub_one_dvd_derivative_of_pow_dvd (ih dvd)

