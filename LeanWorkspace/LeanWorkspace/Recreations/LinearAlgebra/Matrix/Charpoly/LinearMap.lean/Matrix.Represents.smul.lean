import Mathlib

variable {ι : Type*} [Fintype ι]

variable {M : Type*} [AddCommGroup M] (R : Type*) [CommRing R] [Module R M] (I : Ideal R)

variable (b : ι → M)

variable {R} [DecidableEq ι]

theorem Matrix.Represents.smul {A : Matrix ι ι R} {f : Module.End R M} (h : A.Represents b f)
    (r : R) : (r • A).Represents b (r • f) := by
  delta Matrix.Represents at h ⊢
  rw [map_smul, map_smul, h]

