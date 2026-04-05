import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R]

theorem rootMultiplicity_X_sub_C_pow [Nontrivial R] (a : R) (n : ℕ) :
    rootMultiplicity a ((Polynomial.X - Polynomial.C a) ^ n) = n := by
  have := Polynomial.rootMultiplicity_mul_X_sub_C_pow (a := a) (n := n) Polynomial.C.map_one_ne_zero
  rwa [rootMultiplicity_C, map_one, one_mul, zero_add] at this

