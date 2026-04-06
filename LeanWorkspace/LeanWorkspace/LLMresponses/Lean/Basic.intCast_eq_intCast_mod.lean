FAIL
import Mathlib

variable (R : Type*)

variable [AddGroupWithOne R] (p : ℕ) [CharP R p] {a b : ℤ}

theorem intCast_eq_intCast_mod : (a : R) = a % (p : ℤ) := by
  cases p with
  | zero =>
      simp
  | succ p =>
      rw [← Int.mul_ediv_add_emod a (p.succ : ℤ)]
      norm_num [CharP.cast_eq_zero (R := R) (p.succ : ℕ)]
