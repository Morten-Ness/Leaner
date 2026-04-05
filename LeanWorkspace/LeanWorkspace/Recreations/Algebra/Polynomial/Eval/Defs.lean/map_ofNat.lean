import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

variable (f : R →+* S)

theorem map_ofNat (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : R[X]).map f = ofNat(n) := show (n : R[X]).map f = n by rw [Polynomial.map_natCast]

--TODO rename to `map_dvd_map`

