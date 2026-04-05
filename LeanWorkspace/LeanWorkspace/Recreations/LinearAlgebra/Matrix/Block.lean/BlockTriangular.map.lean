import Mathlib

variable {α β m n o : Type*} {m' n' : α → Type*}

variable {R : Type v} {M N : Matrix m m R} {b : m → α}

variable [LT α]

theorem BlockTriangular.map {S F} [FunLike F R S] [Zero R] [Zero S] [ZeroHomClass F R S] (f : F)
    (h : Matrix.BlockTriangular M b) : Matrix.BlockTriangular (M.map f) b := fun i j lt ↦ by simp [h lt]

