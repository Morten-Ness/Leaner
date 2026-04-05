import Mathlib

variable {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R] {P : Polynomial R} {η : R}

theorem signVariations_C_mul (P : Polynomial R) (hx : η ≠ 0) :
    Polynomial.signVariations (C η * P) = Polynomial.signVariations P := by
  wlog! hx2 : 0 < η
  · simpa [lt_of_le_of_ne hx2, hx] using this (η := -η) (P := -P)
  rw [Polynomial.signVariations, Polynomial.signVariations]
  rw [coeffList_C_mul _ (lt_or_lt_iff_ne.mp (.inr hx2)), ← List.comp_map]
  congr 5
  funext
  simp [hx2, sign_mul]

