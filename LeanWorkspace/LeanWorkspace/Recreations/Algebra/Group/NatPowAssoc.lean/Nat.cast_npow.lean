import Mathlib

variable {M : Type*}

variable [Monoid M]

theorem Nat.cast_npow (R : Type*) [NonAssocSemiring R] [Pow R ℕ] [NatPowAssoc R] (n m : ℕ) :
    (↑(n ^ m) : R) = (↑n : R) ^ m := by
  induction m with
  | zero => simp only [pow_zero, Nat.cast_one, npow_zero]
  | succ m ih => rw [npow_add, npow_add, Nat.cast_mul, ih, npow_one, npow_one]

