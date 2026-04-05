import Mathlib

variable {M : Type*}

theorem neg_npow_assoc {R : Type*} [NonAssocRing R] [Pow R ℕ] [NatPowAssoc R] (a b : R) (k : ℕ) :
    (-1) ^ k * a * b = (-1) ^ k * (a * b) := by
  induction k with
  | zero => simp only [npow_zero, one_mul]
  | succ k ih =>
    rw [npow_add, npow_one, ← neg_mul_comm, mul_one]
    simp only [neg_mul, ih]

