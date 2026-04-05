import Mathlib

variable {α β m n o : Type*} {m' n' : α → Type*}

variable {R : Type v} {M N : Matrix m m R} {b : m → α}

variable [LT α]

theorem BlockTriangular.add_iff_left [AddGroup R] (hN : Matrix.BlockTriangular N b) :
    Matrix.BlockTriangular (M + N) b ↔ Matrix.BlockTriangular M b := ⟨(by simpa using ·.sub hN), (·.add hN)⟩

