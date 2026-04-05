import Mathlib

variable {n : Type*} [Fintype n]

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

variable (b : Basis n R M)

theorem ker_toLin_eq_bot [DecidableEq n] (A : Matrix n n R) (hA : IsUnit A.det) :
    LinearMap.ker (toLin b b A) = ⊥ := ker_eq_bot.mpr (Matrix.toLinearEquiv b A hA).injective

