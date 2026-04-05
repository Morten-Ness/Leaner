import Mathlib

variable {α β m n : Type*} {A : Matrix n n α}

variable {R : Type*} [Monoid R] [Star R] [Star α] [MulAction R α] [StarModule R α]

theorem IsHermitian.of_smul' {A : Matrix n n α} {k : R} [Invertible k] (h : (k • A).IsHermitian)
    (hk : IsSelfAdjoint ⅟k) : A.IsHermitian := by
  rw [← invOf_smul_smul k A]
  exact h.smul hk

