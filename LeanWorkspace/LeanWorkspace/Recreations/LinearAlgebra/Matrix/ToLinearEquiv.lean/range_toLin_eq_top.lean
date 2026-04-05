import Mathlib

variable {n : Type*} [Fintype n]

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

variable (b : Basis n R M)

theorem range_toLin_eq_top [DecidableEq n] (A : Matrix n n R) (hA : IsUnit A.det) :
    LinearMap.range (toLin b b A) = ⊤ := range_eq_top.mpr (Matrix.toLinearEquiv b A hA).surjective

