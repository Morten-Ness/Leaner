import Mathlib

variable {α β m n o : Type*} {m' n' : α → Type*}

variable {R : Type v} {M N : Matrix m m R} {b : m → α}

variable [Preorder α]

variable [Zero R]

theorem blockTriangular_blockDiagonal [DecidableEq α] (d : α → Matrix m m R) :
    Matrix.BlockTriangular (blockDiagonal d) Prod.snd := by
  rintro ⟨i, i'⟩ ⟨j, j'⟩ h
  rw [blockDiagonal'_eq_blockDiagonal, Matrix.blockTriangular_blockDiagonal']
  exact h

