import Mathlib

variable {α β m n o : Type*} {m' n' : α → Type*}

variable {R : Type v} {M N : Matrix m m R} {b : m → α}

variable [Preorder α]

variable [Zero R]

variable [DecidableEq m]

theorem blockTriangular_single' {i j : m} (hij : b j ≤ b i) (c : R) :
    Matrix.BlockTriangular (single i j c) (toDual ∘ b) := Matrix.blockTriangular_single (by exact toDual_le_toDual.mpr hij) _

