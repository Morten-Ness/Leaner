import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

variable {M : Matrix m n α} {i : m} {j : n} {b : n → α} {c : m → α}

theorem update_vecMulVec [DecidableEq m] [Mul α] (u : m → α) (v : n → α) (i : m) (a : α) :
    vecMulVec (Function.update u i a) v = (vecMulVec u v).updateRow i (a • v) := by
  ext i' j
  obtain rfl | hi := eq_or_ne i' i
  · simp [vecMulVec_apply]
  · simp [vecMulVec_apply, hi]

