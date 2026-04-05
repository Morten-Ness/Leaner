import Mathlib

open scoped ArithmeticFunction

theorem finMulAntidiag_one {d : ℕ} :
    Nat.finMulAntidiag d 1 = {fun _ => 1} := by
  ext
  simp only [Nat.mem_finMulAntidiag, prod_eq_one_iff, Finset.mem_univ, forall_const, ne_eq, one_ne_zero,
    not_false_eq_true, and_true, mem_singleton]
  grind

