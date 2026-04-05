import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

variable {M : Matrix m n α} {i : m} {j : n} {b : n → α} {c : m → α}

theorem vecMulVec_update [DecidableEq n] [Mul α] (u : m → α) (v : n → α) (j : n) (a : α) :
    vecMulVec u (Function.update v j a) = (vecMulVec u v).updateCol j (MulOpposite.op a • u) := by
  ext i j'
  obtain rfl | hi := eq_or_ne j' j
  · simp [vecMulVec_apply]
  · simp [vecMulVec_apply, hi]

