import Mathlib

open scoped Function -- required for scoped `on` notation

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

variable [Semiring S]

theorem leadingCoeff_map_eq_of_isUnit_leadingCoeff [Nontrivial S] (f : R →+* S)
    (hp : IsUnit p.leadingCoeff) : (p.map f).leadingCoeff = f p.leadingCoeff := leadingCoeff_map_of_leadingCoeff_ne_zero _ <| f.isUnit_map hp |>.ne_zero

