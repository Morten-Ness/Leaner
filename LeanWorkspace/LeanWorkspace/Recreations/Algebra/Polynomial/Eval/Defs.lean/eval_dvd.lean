import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [CommSemiring R] {p q : R[X]} {x : R} [CommSemiring S] (f : R →+* S)

theorem eval_dvd : p ∣ q → Polynomial.eval x p ∣ Polynomial.eval x q := Polynomial.eval₂_dvd _ _

