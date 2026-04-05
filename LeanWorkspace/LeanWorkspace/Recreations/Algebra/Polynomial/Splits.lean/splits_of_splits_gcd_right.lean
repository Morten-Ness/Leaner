import Mathlib

open scoped Polynomial

variable {R : Type*}

variable {F : Type u} {K : Type v} {L : Type w}

variable [CommRing R] [Field K] [Field L] [Field F]

variable (i : K →+* L)

theorem splits_of_splits_gcd_right [DecidableEq K] {f g : K[X]} (hg0 : g ≠ 0)
    (hg : Polynomial.Splits g) : Polynomial.Splits (EuclideanDomain.gcd f g) := Polynomial.Splits.of_dvd hg hg0 <| EuclideanDomain.gcd_dvd_right f g

