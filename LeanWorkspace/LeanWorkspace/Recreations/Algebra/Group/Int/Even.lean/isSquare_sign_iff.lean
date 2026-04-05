import Mathlib

variable {m n : ℤ}

theorem isSquare_sign_iff {z : ℤ} : IsSquare z.sign ↔ 0 ≤ z := by
  induction z using Int.induction_on with
  | zero => simpa using ⟨0, by simp⟩
  | succ => norm_cast; simp
  | pred =>
    rw [sign_eq_neg_one_of_neg (by lia), ← neg_add', Int.neg_nonneg]
    norm_cast
    simp only [reduceNeg, le_zero_eq, Nat.add_eq_zero_iff, succ_ne_self, and_false, iff_false]
    rintro ⟨a | a, ⟨⟩⟩

