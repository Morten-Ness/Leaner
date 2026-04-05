import Mathlib

open scoped Polynomial

variable {R : Type*}

variable {F : Type u} {K : Type v} {L : Type w}

variable [CommRing R] [Field K] [Field L] [Field F]

variable (i : K →+* L)

theorem splits_of_splits_gcd_left [DecidableEq K] {f g : K[X]} (hf0 : f ≠ 0)
    (hf : Polynomial.Splits f) : Polynomial.Splits (EuclideanDomain.gcd f g) := Polynomial.Splits.of_dvd hf hf0 <| EuclideanDomain.gcd_dvd_left f g

