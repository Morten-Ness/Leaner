import Mathlib

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem coeff_pow_of_natDegree_le (pn : p.natDegree ≤ n) :
    (p ^ m).coeff (m * n) = p.coeff n ^ m := by
  induction m with
  | zero => simp
  | succ m hm =>
    rw [pow_succ, pow_succ, ← hm, Nat.succ_mul, coeff_mul_add_eq_of_natDegree_le _ pn]
    refine natDegree_pow_le.trans (le_trans ?_ (le_refl _))
    exact mul_le_mul_of_nonneg_left pn m.zero_le

