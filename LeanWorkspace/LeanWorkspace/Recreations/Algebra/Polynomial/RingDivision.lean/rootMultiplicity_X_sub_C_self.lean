import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R]

theorem rootMultiplicity_X_sub_C_self [Nontrivial R] {x : R} :
    rootMultiplicity x (Polynomial.X - Polynomial.C x) = 1 := pow_one (Polynomial.X - Polynomial.C x) ▸ Polynomial.rootMultiplicity_X_sub_C_pow x 1

