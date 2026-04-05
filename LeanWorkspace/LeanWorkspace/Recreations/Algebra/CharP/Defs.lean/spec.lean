import Mathlib

variable (R : Type*)

variable [NonAssocSemiring R]

theorem spec : ∀ x : ℕ, (x : R) = 0 ↔ ringChar R ∣ x := by
  letI : CharP R (ringChar R) := (Classical.choose_spec (CharP.existsUnique R)).1
  exact CharP.cast_eq_zero_iff R (ringChar R)

