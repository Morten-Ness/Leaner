import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R]

theorem rootMultiplicity_eq_natTrailingDegree {p : R[X]} {t : R} :
    p.rootMultiplicity t = (p.comp (Polynomial.X + Polynomial.C t)).natTrailingDegree := Polynomial.rootMultiplicity_eq_rootMultiplicity.trans rootMultiplicity_eq_natTrailingDegree'

