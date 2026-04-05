import Mathlib

variable {α : Type*}

variable [Ring α] [LinearOrder α] [IsOrderedRing α] {n : ℕ} {a b : α}

theorem abs_mul (a b : α) : |a * b| = |a| * |b| := by
  rw [abs_eq (mul_nonneg (abs_nonneg a) (abs_nonneg b))]
  rcases le_total a 0 with ha | ha <;> rcases le_total b 0 with hb | hb <;>
    simp only [abs_of_nonpos, abs_of_nonneg, true_or, or_true, neg_mul, mul_neg, neg_neg, *]

