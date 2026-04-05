import Mathlib

open scoped Matrix

variable {R : Type u} {n : Type w} [CommRing R] [DecidableEq n] [Fintype n]

variable (J : Matrix n n R)

theorem mem_skewAdjointMatricesLieSubalgebra (A : Matrix n n R) :
    A ∈ skewAdjointMatricesLieSubalgebra J ↔ A ∈ skewAdjointMatricesSubmodule J := Iff.rfl

