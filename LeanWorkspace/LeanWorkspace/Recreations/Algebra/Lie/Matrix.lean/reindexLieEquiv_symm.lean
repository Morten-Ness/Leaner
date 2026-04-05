import Mathlib

open scoped Matrix

variable {R : Type u} [CommRing R]

variable {n : Type w} [DecidableEq n] [Fintype n]

variable {m : Type w₁} [DecidableEq m] [Fintype m] (e : n ≃ m)

theorem reindexLieEquiv_symm :
    (Matrix.reindexLieEquiv e : _ ≃ₗ⁅R⁆ _).symm = Matrix.reindexLieEquiv e.symm := rfl

