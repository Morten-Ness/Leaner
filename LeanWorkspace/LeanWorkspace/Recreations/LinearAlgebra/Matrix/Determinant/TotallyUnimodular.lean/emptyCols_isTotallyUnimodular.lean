import Mathlib

variable {m m' n n' R : Type*} [CommRing R]

theorem emptyCols_isTotallyUnimodular [IsEmpty n] (A : Matrix m n R) :
    A.IsTotallyUnimodular := A.Matrix.emptyRows_isTotallyUnimodular transpose.transpose

