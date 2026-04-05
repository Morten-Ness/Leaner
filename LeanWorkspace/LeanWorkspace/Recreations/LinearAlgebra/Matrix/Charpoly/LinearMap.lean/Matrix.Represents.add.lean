import Mathlib

variable {ι : Type*} [Fintype ι]

variable {M : Type*} [AddCommGroup M] (R : Type*) [CommRing R] [Module R M] (I : Ideal R)

variable (b : ι → M)

variable {R} [DecidableEq ι]

theorem Matrix.Represents.add {A A' : Matrix ι ι R} {f f' : Module.End R M} (h : A.Represents b f)
    (h' : Matrix.Represents b A' f') : (A + A').Represents b (f + f') := by
  delta Matrix.Represents at h h' ⊢; rw [map_add, map_add, h, h']

