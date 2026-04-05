import Mathlib

variable {α β m n o : Type*} {m' n' : α → Type*}

variable {R : Type v} {M N : Matrix m m R} {b : m → α}

variable [Preorder α]

variable [Zero R]

theorem blockTriangular_blockDiagonal' [DecidableEq α] (d : ∀ i : α, Matrix (m' i) (m' i) R) :
    Matrix.BlockTriangular (blockDiagonal' d) Sigma.fst := by
  rintro ⟨i, i'⟩ ⟨j, j'⟩ h
  apply blockDiagonal'_apply_ne d i' j' fun h' => ne_of_lt h h'.symm

