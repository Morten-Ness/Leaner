import Mathlib

variable (n p : Type*) (R : Type u₂) {𝕜 : Type*} [Field 𝕜]

variable [DecidableEq n] [DecidableEq p]

variable [CommRing R]

variable {R n} (i j : n)

theorem det [Fintype n] (t : Matrix.TransvectionStruct n R) : det t.toMatrix = 1 := Matrix.det_transvection_of_ne _ _ t.hij _

