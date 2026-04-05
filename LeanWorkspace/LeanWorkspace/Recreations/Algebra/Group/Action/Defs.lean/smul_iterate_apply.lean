import Mathlib

variable {M N G H α β γ δ : Type*}

variable [Monoid M] [MulAction M α] {a : M}

theorem smul_iterate_apply (a : M) (n : ℕ) (x : α) : (a • ·)^[n] x = a ^ n • x := by
  rw [smul_iterate]

