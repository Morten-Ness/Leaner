import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

variable {M : Matrix m n α} {i : m} {j : n} {b : n → α} {c : m → α}

theorem updateRow_mul [DecidableEq l] [Fintype m] [NonUnitalNonAssocSemiring α]
    (A : Matrix l m α) (i : l) (r : m → α) (B : Matrix m n α) :
    A.updateRow i r * B = (A * B).updateRow i (r ᵥ* B) := by
  ext i' j'
  obtain rfl | hi := eq_or_ne i' i
  · simp [mul_apply, vecMul, dotProduct]
  · simp [mul_apply, hi]

