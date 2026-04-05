import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

variable {M : Matrix m n α} {i : m} {j : n} {b : n → α} {c : m → α}

theorem mul_updateCol [DecidableEq n] [Fintype m] [NonUnitalNonAssocSemiring α]
    (A : Matrix l m α) (B : Matrix m n α) (j : n) (c : m → α) :
    A * B.updateCol j c = (A * B).updateCol j (A *ᵥ c) := by
  ext i' j'
  obtain rfl | hj := eq_or_ne j' j
  · simp [mul_apply, mulVec, dotProduct]
  · simp [mul_apply, hj]

