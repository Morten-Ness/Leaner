import Mathlib

variable {α β m n : Type*} {A : Matrix n n α}

variable {R : Type*} [Star R] [Star α] [SMul R α] [StarModule R α]

theorem IsHermitian.smul {A : Matrix n n α} (h : A.IsHermitian) {k : R} (hk : IsSelfAdjoint k) :
    (k • A).IsHermitian := by
  rw [Matrix.IsHermitian, conjTranspose_smul, hk.star_eq, h.eq]

