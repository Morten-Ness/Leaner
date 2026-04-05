import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [Ring R] {p q : R[X]}

theorem map_modByMonic [Ring S] (f : R →+* S) (hq : Polynomial.Monic q) :
    (p %ₘ q).map f = p.map f %ₘ q.map f := (Polynomial.map_mod_divByMonic f hq).2

