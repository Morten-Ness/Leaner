import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {a b : R} {n : ℕ}

variable [CommRing R] {p p₁ p₂ q : R[X]}

theorem rootMultiplicity_eq_zero {p : R[X]} {x : R} (h : ¬IsRoot p x) : Polynomial.rootMultiplicity x p = 0 := Polynomial.rootMultiplicity_eq_zero_iff.2 fun h' => (h h').elim

