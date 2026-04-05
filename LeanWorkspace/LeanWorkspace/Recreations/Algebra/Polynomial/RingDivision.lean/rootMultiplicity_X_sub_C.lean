import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R]

theorem rootMultiplicity_X_sub_C [Nontrivial R] [DecidableEq R] {x y : R} :
    rootMultiplicity x (Polynomial.X - Polynomial.C y) = if x = y then 1 else 0 := by
  split_ifs with hxy
  · rw [hxy]
    exact Polynomial.rootMultiplicity_X_sub_C_self
  exact rootMultiplicity_eq_zero (mt root_X_sub_C.mp (Ne.symm hxy))

