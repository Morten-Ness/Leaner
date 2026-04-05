import Mathlib

variable {R K : Type*} [CommRing R] [Field K]

theorem isParabolic_iff_of_upperTriangular {g : GL (Fin 2) K} (hg : g 1 0 = 0) :
    g.IsParabolic ↔ g 0 0 = g 1 1 ∧ g 0 1 ≠ 0 := Matrix.isParabolic_iff_of_upperTriangular hg

