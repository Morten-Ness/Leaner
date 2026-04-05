import Mathlib

variable {R : Type*}

variable [Semiring R]

theorem IsMonicOfDegree.pow {p : R[X]} {m : ℕ} (hp : IsMonicOfDegree p m) (n : ℕ) :
    IsMonicOfDegree (p ^ n) (m * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_add, mul_one]
    exact ih.mul hp

