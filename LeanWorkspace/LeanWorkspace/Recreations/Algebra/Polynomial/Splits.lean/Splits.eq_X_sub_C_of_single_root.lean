import Mathlib

variable {R : Type*}

variable [CommRing R] {f g : R[X]} {A B : Type*} [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B] [Algebra R A] [Algebra R B]

variable [IsDomain R]

theorem Splits.eq_X_sub_C_of_single_root (hf : Polynomial.Splits f) {x : R} (hr : f.roots = {x}) :
    f = C f.leadingCoeff * (X - C x) := by
  rw [hf.eq_prod_roots, hr]
  simp

