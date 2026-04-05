import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q : R[X]} {ι : Type*}

theorem ne_zero_of_natDegree_gt {n : ℕ} (h : n < natDegree p) : p ≠ 0 := fun H => by
  simp [H] at h

