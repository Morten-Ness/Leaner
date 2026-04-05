import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommRing R] {p : R[X]} {t : R}

theorem aeval_neg {p : R[X]} [Ring A] [Algebra R A] (x : A) :
    Polynomial.aeval x (-p) = -Polynomial.aeval x p := map_neg ..

