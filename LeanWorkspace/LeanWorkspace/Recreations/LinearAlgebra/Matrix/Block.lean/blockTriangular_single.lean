import Mathlib

variable {α β m n o : Type*} {m' n' : α → Type*}

variable {R : Type v} {M N : Matrix m m R} {b : m → α}

variable [Preorder α]

variable [Zero R]

variable [DecidableEq m]

theorem blockTriangular_single {i j : m} (hij : b i ≤ b j) (c : R) :
    Matrix.BlockTriangular (single i j c) b := by
  intro r s hrs
  apply single_apply_of_ne
  rintro ⟨rfl, rfl⟩
  exact (hij.trans_lt hrs).false

