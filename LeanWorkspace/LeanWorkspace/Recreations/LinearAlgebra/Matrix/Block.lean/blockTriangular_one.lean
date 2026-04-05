import Mathlib

variable {α β m n o : Type*} {m' n' : α → Type*}

variable {R : Type v} {M N : Matrix m m R} {b : m → α}

variable [Preorder α]

variable [Zero R]

variable [DecidableEq m]

theorem blockTriangular_one [One R] : Matrix.BlockTriangular (1 : Matrix m m R) b := Matrix.blockTriangular_diagonal _

