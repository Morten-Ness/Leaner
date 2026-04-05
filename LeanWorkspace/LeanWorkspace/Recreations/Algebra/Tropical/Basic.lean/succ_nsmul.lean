import Mathlib

variable (R : Type u)

variable [LinearOrderedAddCommMonoidWithTop R]

theorem succ_nsmul {R} [LinearOrder R] [OrderTop R] (x : Tropical R) (n : ℕ) : (n + 1) • x = x := by
  induction n with
  | zero => simp [one_nsmul]
  | succ n IH => rw [add_nsmul, IH, one_nsmul, Tropical.add_self]

-- TODO: find/create the right classes to make this hold (for enat, ennreal, etc)
-- Requires `zero_eq_bot` to be true
-- lemma Tropical.add_eq_zero_iff {a b : tropical R} :
--   a + b = 1 ↔ a = 1 ∨ b = 1 := sorry

