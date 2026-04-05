import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

variable (f : R →+* S)

theorem map_dvd (f : R →+* S) {x y : R[X]} : x ∣ y → x.map f ∣ y.map f := _root_.map_dvd (Polynomial.mapRingHom f)

