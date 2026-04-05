import Mathlib

open scoped Matrix

variable {R : Type u} [CommRing R]

variable {n : Type w} [DecidableEq n] [Fintype n]

theorem lieConj_symm_apply (P A : Matrix n n R) (h : Invertible P) :
    (P.lieConj h).symm A = P⁻¹ * A * P := by
  simp [LinearEquiv.symm_conj_apply, Matrix.lieConj, LinearMap.toMatrix'_comp,
    LinearMap.toMatrix'_toLin']

