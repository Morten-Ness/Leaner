import Mathlib

open scoped Polynomial

variable {R : Type*}

variable {F : Type u} {K : Type v} {L : Type w}

variable [CommRing K] [Field L] [Field F]

variable (i : K →+* L)

theorem splits_map_iff {L : Type*} [CommRing L] (i : K →+* L) (j : L →+* F) {f : K[X]} :
    Polynomial.Splits ((f.map i).map j) ↔ Polynomial.Splits (f.map (j.comp i)) := by
  rw [Polynomial.map_map]

