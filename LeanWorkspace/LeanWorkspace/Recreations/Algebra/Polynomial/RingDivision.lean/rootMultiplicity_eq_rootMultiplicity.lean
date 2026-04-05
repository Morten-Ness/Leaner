import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

variable [CommRing R]

theorem rootMultiplicity_eq_rootMultiplicity {p : R[X]} {t : R} :
    p.rootMultiplicity t = (p.comp (Polynomial.X + Polynomial.C t)).rootMultiplicity 0 := by
  classical
  simp_rw [rootMultiplicity_eq_multiplicity, comp_X_add_C_eq_zero_iff]
  congr 1
  rw [C_0, sub_zero]
  convert (multiplicity_map_eq <| algEquivAevalXAddC t).symm using 2
  simp [C_eq_algebraMap]

