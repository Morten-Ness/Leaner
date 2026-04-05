import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

variable {M : Matrix m n α} {i : m} {j : n} {b : n → α} {c : m → α}

theorem updateRow_mulVec [DecidableEq l] [Fintype m] [NonUnitalNonAssocSemiring α]
    (A : Matrix l m α) (i : l) (c : m → α) (v : m → α) :
    A.updateRow i c *ᵥ v = Function.update (A *ᵥ v) i (c ⬝ᵥ v) := by
  ext i'
  obtain rfl | hi := eq_or_ne i' i
  · simp [mulVec]
  · simp [mulVec, hi]

