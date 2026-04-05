import Mathlib

variable {α β m n o : Type*} {m' n' : α → Type*}

variable {R : Type v} {M N : Matrix m m R} {b : m → α}

variable [LT α]

theorem BlockTriangular.add_iff_right [AddGroup R] (hM : Matrix.BlockTriangular M b) :
    Matrix.BlockTriangular (M + N) b ↔ Matrix.BlockTriangular N b := ⟨(by simpa using hM.neg.add ·), hM.add⟩

