import Mathlib

variable {R : Type*}

variable [CommRing R] {f g : R[X]} {A B : Type*} [CommRing A] [CommRing B]
  [IsDomain A] [IsDomain B] [Algebra R A] [Algebra R B]

variable [IsDomain R]

theorem Splits.splits (hf : Polynomial.Splits f) :
    f = 0 ∨ ∀ {g : R[X]}, Irreducible g → g ∣ f → degree g ≤ 1 := or_iff_not_imp_left.mpr fun hf0 _ hg hgf ↦ degree_le_of_natDegree_le <|
    (hf.of_dvd hf0 hgf).natDegree_le_one_of_irreducible hg

