import Mathlib

variable {α β m n o : Type*} {m' n' : α → Type*}

variable {R : Type v} {M N : Matrix m m R} {b : m → α}

variable [Preorder α]

variable [Zero R]

theorem blockTriangular_diagonal [DecidableEq m] (d : m → R) : Matrix.BlockTriangular (diagonal d) b := fun _ _ h => diagonal_apply_ne' d fun h' => ne_of_lt h (congr_arg _ h')

