import Mathlib

variable {α β m n o : Type*} {m' n' : α → Type*}

variable {R : Type v} {M N : Matrix m m R} {b : m → α}

variable [Preorder α]

variable [CommRing R] [DecidableEq m]

theorem blockTriangular_transvection {i j : m} (hij : b i ≤ b j) (c : R) :
    Matrix.BlockTriangular (transvection i j c) b := Matrix.blockTriangular_one.add (Matrix.blockTriangular_single hij c)

