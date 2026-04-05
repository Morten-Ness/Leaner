import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {m n : ℕ} {ι : Type y}

variable [Semiring R] {p : R[X]}

theorem Monic.isRegular {R : Type*} [Ring R] {p : R[X]} (hp : Polynomial.Monic p) : IsRegular p := by
  constructor
  · intro q r h
    dsimp only at h
    rw [← sub_eq_zero, ← hp.mul_right_eq_zero_iff, mul_sub, h, sub_self]
  · intro q r h
    simp only at h
    rw [← sub_eq_zero, ← hp.mul_left_eq_zero_iff, sub_mul, h, sub_self]

