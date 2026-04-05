import Mathlib

variable {R : Type*}

variable [AddCommGroupWithOne R] [PartialOrder R] [AddLeftMono R]

variable [ZeroLEOneClass R]

theorem cast_mono : Monotone (Int.cast : ℤ → R) := by
  intro m n h
  rw [← sub_nonneg] at h
  lift n - m to ℕ using h with k hk
  rw [← sub_nonneg, ← cast_sub, ← hk, cast_natCast]
  exact k.cast_nonneg'

