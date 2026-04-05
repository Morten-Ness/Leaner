import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

variable [CommSemiring R] {p q : R[X]} {x : R} [CommSemiring S] (f : R →+* S)

theorem coe_compRingHom_apply (p q : R[X]) : (Polynomial.compRingHom q : R[X] → R[X]) p = Polynomial.comp p q := rfl

