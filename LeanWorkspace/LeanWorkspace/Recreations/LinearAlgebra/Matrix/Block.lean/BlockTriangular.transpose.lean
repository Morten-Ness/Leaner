import Mathlib

variable {α β m n o : Type*} {m' n' : α → Type*}

variable {R : Type v} {M N : Matrix m m R} {b : m → α}

variable [LT α]

variable [Zero R]

theorem BlockTriangular.transpose :
    M.BlockTriangular b → Mᵀ.BlockTriangular (toDual ∘ b) := swap

