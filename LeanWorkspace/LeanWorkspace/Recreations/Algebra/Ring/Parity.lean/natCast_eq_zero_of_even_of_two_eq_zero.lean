import Mathlib

variable {F α β : Type*}

variable {R : Type*} [AddMonoidWithOne R]

private theorem natCast_eq_zero_or_one_of_two_eq_zero' (n : ℕ) (h : (2 : R) = 0) :
    (Even n → (n : R) = 0) ∧ (Odd n → (n : R) = 1) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n _ _ => simpa [add_assoc, Nat.even_add_one, Nat.odd_add_one, h]


theorem natCast_eq_zero_of_even_of_two_eq_zero {n : ℕ} (hn : Even n) (h : (2 : R) = 0) :
    (n : R) = 0 := (natCast_eq_zero_or_one_of_two_eq_zero' n h).1 hn

