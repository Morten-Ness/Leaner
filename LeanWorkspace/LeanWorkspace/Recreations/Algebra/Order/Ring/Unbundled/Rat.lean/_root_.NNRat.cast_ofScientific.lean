import Mathlib

variable {a b c p q : ℚ}

theorem _root_.NNRat.cast_ofScientific {K} [NNRatCast K] (m : ℕ) (s : Bool) (e : ℕ) :
    (OfScientific.ofScientific m s e : ℚ≥0) = (OfScientific.ofScientific m s e : K) := rfl

protected lemma divInt_le_divInt {a b c d : ℤ} (b0 : 0 < b) (d0 : 0 < d) :
    a /. b ≤ c /. d ↔ a * d ≤ c * b := by
  rw [Rat.le_iff_sub_nonneg, ← Int.sub_nonneg]
  simp [sub_eq_add_neg, ne_of_gt b0, ne_of_gt d0, Int.mul_pos d0 b0]

protected lemma lt_iff_le_not_ge (a b : ℚ) : a < b ↔ a ≤ b ∧ ¬b ≤ a :=
  Std.LawfulOrderLT.lt_iff a b

