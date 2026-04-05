import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] [Semiring S] {p q r : R[X]}

theorem ite_le_natDegree_coeff (p : R[X]) (n : ℕ) (I : Decidable (n < 1 + natDegree p)) :
    @ite _ (n < 1 + natDegree p) I (coeff p n) 0 = coeff p n := by
  split_ifs with h
  · rfl
  · exact (Polynomial.coeff_eq_zero_of_natDegree_lt (not_le.1 fun w => h (Nat.lt_one_add_iff.2 w))).symm

