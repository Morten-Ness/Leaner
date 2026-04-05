import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R]

theorem iterate_derivative_mul {n} (p q : R[X]) :
    Polynomial.derivative^[n] (p * q) =
      ∑ k ∈ range n.succ, (n.choose k • (Polynomial.derivative^[n - k] p * Polynomial.derivative^[k] q)) := by
  induction n with
  | zero =>
    simp [Finset.range]
  | succ n IH =>
    calc
      Polynomial.derivative^[n + 1] (p * q) =
          Polynomial.derivative (∑ k ∈ range n.succ,
              n.choose k • (Polynomial.derivative^[n - k] p * Polynomial.derivative^[k] q)) := by
        rw [Function.iterate_succ_apply', IH]
      _ = (∑ k ∈ range n.succ,
            n.choose k • (Polynomial.derivative^[n - k + 1] p * Polynomial.derivative^[k] q)) +
          ∑ k ∈ range n.succ,
            n.choose k • (Polynomial.derivative^[n - k] p * Polynomial.derivative^[k + 1] q) := by
        simp_rw [Polynomial.derivative_sum, Polynomial.derivative_smul, Polynomial.derivative_mul, Function.iterate_succ_apply',
          smul_add, sum_add_distrib]
      _ = (∑ k ∈ range n.succ,
                n.choose k.succ • (Polynomial.derivative^[n - k] p * Polynomial.derivative^[k + 1] q)) +
              1 • (Polynomial.derivative^[n + 1] p * Polynomial.derivative^[0] q) +
            ∑ k ∈ range n.succ, n.choose k • (Polynomial.derivative^[n - k] p * Polynomial.derivative^[k + 1] q) :=
        ?_
      _ = ((∑ k ∈ range n.succ, n.choose k • (Polynomial.derivative^[n - k] p * Polynomial.derivative^[k + 1] q)) +
              ∑ k ∈ range n.succ,
                n.choose k.succ • (Polynomial.derivative^[n - k] p * Polynomial.derivative^[k + 1] q)) +
            1 • (Polynomial.derivative^[n + 1] p * Polynomial.derivative^[0] q) := by
        rw [add_comm, add_assoc]
      _ = (∑ i ∈ range n.succ,
              (n + 1).choose (i + 1) • (Polynomial.derivative^[n + 1 - (i + 1)] p * Polynomial.derivative^[i + 1] q)) +
            1 • (Polynomial.derivative^[n + 1] p * Polynomial.derivative^[0] q) := by
        simp_rw [Nat.choose_succ_succ, Nat.succ_sub_succ, add_smul, sum_add_distrib]
      _ = ∑ k ∈ range n.succ.succ,
            n.succ.choose k • (Polynomial.derivative^[n.succ - k] p * Polynomial.derivative^[k] q) := by
        rw [sum_range_succ' _ n.succ, Nat.choose_zero_right, tsub_zero]
    congr
    refine (sum_range_succ' _ _).trans (congr_arg₂ (· + ·) ?_ ?_)
    · rw [sum_range_succ, Nat.choose_succ_self, zero_smul, add_zero]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [mem_range] at hk
      congr
      lia
    · rw [Nat.choose_zero_right, tsub_zero]

