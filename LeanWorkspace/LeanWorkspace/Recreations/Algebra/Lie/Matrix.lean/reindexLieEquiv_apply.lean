import Mathlib

open scoped Matrix

variable {R : Type u} [CommRing R]

variable {n : Type w} [DecidableEq n] [Fintype n]

variable {m : Type w₁} [DecidableEq m] [Fintype m] (e : n ≃ m)

theorem reindexLieEquiv_apply (M : Matrix n n R) :
    Matrix.reindexLieEquiv e M = Matrix.reindex e e M := rfl

