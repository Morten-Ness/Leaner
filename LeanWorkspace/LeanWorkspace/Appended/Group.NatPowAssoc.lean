import Mathlib

section

variable {M : Type*}

variable [Monoid M]

theorem Nat.cast_npow (R : Type*) [NonAssocSemiring R] [Pow R ℕ] [NatPowAssoc R] (n m : ℕ) :
    (↑(n ^ m) : R) = (↑n : R) ^ m := by
  induction m with
  | zero => simp only [pow_zero, Nat.cast_one, npow_zero]
  | succ m ih => rw [npow_add, npow_add, Nat.cast_mul, ih, npow_one, npow_one]

end

section

variable {M : Type*}

theorem neg_npow_assoc {R : Type*} [NonAssocRing R] [Pow R ℕ] [NatPowAssoc R] (a b : R) (k : ℕ) :
    (-1) ^ k * a * b = (-1) ^ k * (a * b) := by
  induction k with
  | zero => simp only [npow_zero, one_mul]
  | succ k ih =>
    rw [npow_add, npow_one, ← neg_mul_comm, mul_one]
    simp only [neg_mul, ih]

end

section

variable {M : Type*}

variable [MulOneClass M] [Pow M ℕ] [NatPowAssoc M]

theorem npow_mul' (x : M) (m n : ℕ) : x ^ (m * n) = (x ^ n) ^ m := by
  rw [mul_comm]
  exact npow_mul x n m

end

section

variable {M : Type*}

variable [MulOneClass M] [Pow M ℕ] [NatPowAssoc M]

theorem npow_mul (x : M) (m n : ℕ) : x ^ (m * n) = (x ^ m) ^ n := by
  induction n with
  | zero => rw [npow_zero, mul_zero, npow_zero]
  | succ n ih => rw [mul_add, npow_add, ih, mul_one, npow_add, npow_one]

end

section

variable {M : Type*}

variable [MulOneClass M] [Pow M ℕ] [NatPowAssoc M]

theorem npow_mul_assoc (k m n : ℕ) (x : M) :
    (x ^ k * x ^ m) * x ^ n = x ^ k * (x ^ m * x ^ n) := by
  simp only [← npow_add, add_assoc]

end

section

variable {M : Type*}

variable [MulOneClass M] [Pow M ℕ] [NatPowAssoc M]

theorem npow_mul_comm (m n : ℕ) (x : M) :
    x ^ m * x ^ n = x ^ n * x ^ m := by simp only [← npow_add, add_comm]

end
