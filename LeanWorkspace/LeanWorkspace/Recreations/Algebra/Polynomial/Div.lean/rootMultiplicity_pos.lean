import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R] {p p₁ p₂ q : R[X]}

theorem rootMultiplicity_pos {p : R[X]} (hp : p ≠ 0) {x : R} :
    0 < Polynomial.rootMultiplicity x p ↔ IsRoot p x := Polynomial.rootMultiplicity_pos'.trans (and_iff_right hp)

