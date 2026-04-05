import Mathlib

variable {α β m n : Type*} {A : Matrix n n α}

variable {R : Type*} [Monoid R] [Star R] [Star α] [MulAction R α] [StarModule R α]

theorem IsHermitian.of_smul {A : Matrix n n α} {k : R} [Invertible k] (h : (k • A).IsHermitian)
    (hk : IsSelfAdjoint k) : A.IsHermitian := by
  rw [Matrix.IsHermitian, conjTranspose_smul, hk.star_eq] at h
  simpa using congr(⅟k • $h)

