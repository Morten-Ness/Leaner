import Mathlib

variable {G : Type*}

theorem npowBinRec.go_spec {M : Type*} [Semigroup M] [One M] (k : ℕ) (m n : M) :
    npowBinRec.go (k + 1) m n = m * npowRec' (k + 1) n := by
  unfold go
  generalize hk : k + 1 = k'
  replace hk : k' ≠ 0 := by lia
  induction k' using Nat.binaryRecFromOne generalizing n m with
  | zero => simp at hk
  | one => simp [npowRec']
  | bit b k' k'0 ih =>
    rw [Nat.binaryRec_eq _ _ (Or.inl rfl), ih _ _ k'0]
    cases b <;> simp only [Nat.bit, cond_false, cond_true, npowRec'_two_mul]
    rw [npowRec'_succ (by lia), npowRec'_two_mul, ← npowRec'_two_mul,
      ← npowRec'_mul_comm (by lia), mul_assoc]

