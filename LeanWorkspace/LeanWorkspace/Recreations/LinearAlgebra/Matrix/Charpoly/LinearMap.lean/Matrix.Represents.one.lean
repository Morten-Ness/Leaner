import Mathlib

variable {ι : Type*} [Fintype ι]

variable {M : Type*} [AddCommGroup M] (R : Type*) [CommRing R] [Module R M] (I : Ideal R)

variable (b : ι → M)

variable {R} [DecidableEq ι]

theorem Matrix.Represents.one : (1 : Matrix ι ι R).Represents b 1 := by
  delta Matrix.Represents PiToModule.fromMatrix
  rw [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, map_one]
  ext
  rfl

