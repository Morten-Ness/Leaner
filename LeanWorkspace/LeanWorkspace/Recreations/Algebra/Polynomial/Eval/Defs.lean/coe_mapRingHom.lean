import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

variable (f : R →+* S)

theorem coe_mapRingHom (f : R →+* S) : ⇑(Polynomial.mapRingHom f) = Polynomial.map f := rfl

-- This is protected to not clash with the global `map_natCast`.

