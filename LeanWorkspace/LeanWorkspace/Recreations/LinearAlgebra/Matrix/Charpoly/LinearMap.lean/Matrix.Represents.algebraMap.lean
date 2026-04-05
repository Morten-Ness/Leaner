import Mathlib

variable {ι : Type*} [Fintype ι]

variable {M : Type*} [AddCommGroup M] (R : Type*) [CommRing R] [Module R M] (I : Ideal R)

variable (b : ι → M)

variable {R} [DecidableEq ι]

theorem Matrix.Represents.algebraMap (r : R) :
    (algebraMap _ (Matrix ι ι R) r).Represents b (algebraMap _ (Module.End R M) r) := by
  simpa only [Algebra.algebraMap_eq_smul_one] using Matrix.Represents.one.smul r

